## this module produces SMTIr code from NIR
import Nim/compiler/nir/nirinsts except build
import Nim/compiler/nir/nirfiles
import Nim/compiler/ic/bitabs
import smtir
import irtypes
import std/tables
import std/math
import std/sets
import packed_syms
import Nim/compiler/nir/nirtypes except Literals
{.experimental: "inferGenericTypes".}

type
  SymCounter = object
    symModifies: CountTable[SymId]

    frozen: bool
    frozenModifies: CountTable[SymId]

using gen: var SymCounter
proc freeze(gen) =
  ## Freeze syms. It means that old syms values was frozen
  ## and can be used via withOldSym
  gen.frozen = true
  gen.frozenModifies = gen.symModifies

proc unfreeze(gen) =
  gen.frozen = false

proc inc(gen; s: SymId) =
  inc(gen.symModifies, s)

proc oldSymModifies(gen: SymCounter; s: SymId): int =
  if gen.frozen: gen.frozenModifies[s]
  else: gen.symModifies[s] - 1  

proc `[]`(gen: SymCounter; s: SymId): PackedSymId =
  s.toPacked(uint16 gen.symModifies[s])

template withOldSym(gen: SymCounter, s: SymId, body) =
  let modifies = gen.symModifies[s]
  gen.symModifies[s] = gen.oldSymModifies(s) #count(gen.oldSym s).int
  body
  gen.symModifies[s] = modifies

template withNextSym(gen: SymCounter, s: SymId, body) =
  gen.symModifies.inc s
  body
  gen.symModifies.inc s, -1



type
  PhiId = uint32
  GeneratorCtx = object
    m: NirModule
    tree: smtir.Tree
    lit: Literals
    syms: SymCounter

    stack: seq[smtir.Tree] # lvalues stack, need to say that will be after 
                           # current lvalue from rvalue
    labels: Table[LabelId, NodePos]
    # Generate dets:
    currentDet: smtir.Tree
    ways: Table[LabelId, smtir.Tree]
    currentLabel: LabelId
    visitedLabels: HashSet[LabelId]
    
    dets: Table[PackedSymId, smtir.Tree]

import Nim/compiler/nir/nirlineinfos

proc genType(
  c: var GeneratorCtx; 
  tree: var smtir.Tree;
  types: nirtypes.TypeGraph; 
  lit: nirtypes.Literals; 
  t: nirtypes.TypeId; 
  info: PackedLineInfo
  ) =
  template typ(t: irtypes.TypeId): untyped = addTyped(tree, info, t)

  case types[t].kind
  of IntTy:
    case types[t].integralBits
    of 8: typ Int8Id
    of 16: typ Int16Id
    of 32: typ Int32Id
    of 64: typ Int64Id
    else: raiseAssert "Can't generate type"
  of UIntTy:
    case types[t].integralBits
    of 8: typ UInt8Id
    of 16: typ UInt16Id
    of 32: typ UInt32Id
    of 64: typ UInt64Id
    else: raiseAssert "Can't generate type"
  of FloatTy:
    case types[t].integralBits
    of 32: typ Float32Id
    of 64: typ Float64Id
    else: raiseAssert "Can't generate type"
  of BoolTy: typ Bool8Id
  of CharTy: typ UInt8Id # maybe...
  else:
    raiseAssert "Can't generate type"

template buildCheck(typ, body): untyped =
  # lvalues
  block:
    var tree {.inject.} = smtir.Tree()
    tree.build info, Checked:
      tree.addImmediateVal info, 0
      tree.addCheckType info, typ
      body
    
    c.stack.add tree

template buildOverflowCheck(body): untyped =
  buildCheck Overflow:
    body

template binOp(op, typ, a, b) =
  c.tree.build info, op:
    gen c, t, a
    gen c, t, b

template binOp(op) =
  let (typ, _, a, b) = sons4(t, n)
  binOp(op, typ, a, b)

template checkedBinOp(op) =
  let (typ, _, a, b) = sons4(t, n)
  binOp(op, typ, a, b)

  let checkVal = 2'u64 ^ (c.m.types[t[typ].typeId].integralBits - 1)
  buildOverflowCheck:
    tree.build info, Le:
      let s =
        if t[a].kind == SymUse: a
        elif t[b].kind == SymUse: b
        else: raiseAssert "No symbols in bin op"
      
      withNextSym c.syms, t[s].symId:
        tree.addSymUse info, c.syms[t[s].symId]
      
      tree.build info, Scalar:
        genType c, tree, c.m.types, c.m.lit, t[typ].typeId, info
        tree.addIntVal c.lit.numbers, info, cast[int64](checkVal - 1)
  
  buildOverflowCheck:
    tree.build info, Le:
      tree.build info, Scalar:
        genType c, tree, c.m.types, c.m.lit, t[typ].typeId, info
        tree.addIntVal c.lit.numbers, info, -cast[int64](checkVal)
      
      let s =
        if t[a].kind == SymUse: a
        elif t[b].kind == SymUse: b
        else: raiseAssert "No symbols in bin op"
      
      withNextSym c.syms, t[s].symId:
        tree.addSymUse info, c.syms[t[s].symId]


proc genDefaultVal(c: var GeneratorCtx; types: nirtypes.TypeGraph; lit: nirtypes.Literals; t: nirtypes.TypeId; info: PackedLineInfo) =
  # adds a default scalar for type
  c.tree.build info, Scalar: # arrays currently not supported
    genType c, c.tree, types, lit, t, info
    case types[t].kind
    of IntTy, UintTy, BoolTy, CharTy, FloatTy:
      c.tree.addIntVal c.lit.numbers, info, 0
    else: raiseAssert "can't get default val"

proc addLValues(c: var GeneratorCtx) =
  for i in c.stack:
    copyTree(c.tree, i)
  c.stack = @[]

template withTree(c: var GeneratorCtx; t: var smtir.Tree, body) =
  var tree = c.tree

  c.tree = t
  body
  t = c.tree

  c.tree = tree

template overrideTree(c: var GeneratorCtx; res: var smtir.Tree, body) =
  var tree = smtir.Tree()
  withTree c, tree:
    body
  res = tree

proc gen(c: var GeneratorCtx, t: nirinsts.Tree, n: NodePos)
proc buildEquals(
  c: var GeneratorCtx; 
  tree: nirinsts.Tree;
  info: PackedLineInfo,
  selector, values: NodePos
  ) =
  # TODO: if a or b == false or true, then make simpler expr, not a == false  
  case tree[values].kind
  of SelectValue:
    c.tree.build info, Eq:
      gen(c, tree, selector)
      gen(c, tree, values)
  of SelectList:
    if rawOperand(tree[values]) > 1: # len
      var val = default(smtir.Tree)
      withTree c, val:
        for ch in sons(tree, values):
          buildEquals(c, tree, info, selector, ch)
      val = buildNestList(Or, info, val)
      when true:
        var s = ""
        render(val, s, c.lit)
        echo "RENDERED:  ", s
      copyTree(c.tree, val)
    else:
      # else branch
      discard
  else:
    raiseAssert "Unsupported"

proc gen(c: var GeneratorCtx, t: nirinsts.Tree, n: NodePos) =
  let info = t[n].info
  if c.currentLabel in c.visitedLabels and t[n].kind != Label: return # node after visited label
  case t[n].kind
  of SymUse:
    let s = t[n].symId
    c.tree.addSymUse info, c.syms[s]
  of SummonGlobal, Summon:
    let (typ, def) = sons2(t, n)
    c.tree.build info, SymAsgn:
      gen(c, t, def) # update modifiers counter
      genDefaultVal c, c.m.types, c.m.lit, t[typ].typeId, info
  of SymDef:
    let s = t[n].symId
    c.syms.inc s
    c.tree.addSymUse info, c.syms[s]
  of Typed:
    genType c, c.tree, c.m.types, c.m.lit, t[n].typeId, info

  of NumberConv:
    let (typ, arg) = sons2(t, n)

    c.tree.build info, Scalar:
      gen(c, t, typ) # Typed
      gen(c, t, arg)

  of Asgn:
    let (_, le, ri) = sons3(t, n)
    let s = t[le].symId
    c.syms.inc s
    c.dets[c.syms[s]] = c.currentDet

    c.tree.build info, SymAsgn:
      c.gen(t, le) # This symId is modified by old symId, so current symId and oldSym id is same symId
      withOldSym c.syms, s:
        c.gen(t, ri)
    c.addLValues

  of IntVal: c.tree.addIntVal(c.lit.numbers, info, c.m.lit.numbers[t[n].litId])
  
  of CheckedAdd: checkedBinOp(Add)
  of CheckedDiv: checkedBinOp(Div)
  of CheckedMod: checkedBinOp(Mod)
  of CheckedMul: checkedBinOp(Mul)

  of CheckedGoto: discard "L0 ?"

  of Goto:
    c.syms.freeze()

    let lab = t[n].label
    c.ways[lab] = c.currentDet
    incl(c.visitedLabels, lab)
    var i = NodePos(c.labels[lab].uint32 + 1)
    let len = t.len
    while i.int < t.len and t[i].kind notin {Label, LoopLabel}:
      when isMainModule: echo "goto get node: ", t[i].kind
      gen(c, t, i)
      next t, i

  of SelectValue: gen(c, t, n.firstSon)

  of SelectPair:
    let (le, ri) = sons2(t, n)
    # should generate equals, for false is can be just not, for true just expr
    gen(c, t, le)
    gen(c, t, ri)

  of Select:
    let
      (_, selector) = sons2(t, n)
      det = c.currentDet

    var conds: seq[smtir.Tree] = @[]
    for ch in sonsFromN(t, n, 2):
      assert t[ch].kind == SelectPair
      let (values, action) = sons2(t, ch)
      var cond = smtir.Tree()
      withTree c, cond: buildEquals(c, t, info, selector, values)
      if cond.len == 0: continue # skip else branch in case because we will get it in control flow
      conds.add cond
      overrideTree c, c.currentDet:
        if c.currentDet.len > 0:
          c.tree.build info, And:
            copyTree(c.tree, cond)
            copyTree(c.tree, c.currentDet)
        else:
          c.tree = cond
      gen(c, t, action)
      
    var nextBlock = default(smtir.Tree)
    template binOpIf(cond, t, opc, body): untyped =
      overrideTree c, t:
        if cond:
          t.build info, opc:
            copyTree(c.tree, t)
            body
        else:
          c.tree = t

    nextBlock.build info, Not:
      copyTree(nextBlock, buildNestList(Or, info, conds))
    
    binOpIf(
      det.len > 0, 
      nextBlock, And, copyTree(c.tree, det))
    
    c.currentDet = nextBlock

  of Label:
    let lab = t[n].label
    c.currentLabel = lab
    if lab notin c.ways:
      c.currentDet = default(smtir.Tree)
      c.syms.unfreeze()
  else:
    raiseAssert $t[n].kind & " is not supported"

proc findLabels(c: var GeneratorCtx, t: nirinsts.Tree) =
  var i = NodePos(0)
  while i.int < t.len:
    if t[i].kind == Label:#in {Label, LoopLabel}:
      c.labels[t[i].label] = i
    next t, i

proc gen(c: var GeneratorCtx, t: nirinsts.Tree) =
  var i = NodePos(0)
  while i.int < t.len:
    gen c, t, i
    next t, i

when isMainModule:
  import std/[os, osproc]
  import std/compilesettings
  import std/strutils
  const nimCache = querySetting(SingleValueSetting.nimcacheDir).parentDir

  if paramCount() < 1:
    raise newException(CatchableError, "Expected filename")

  let (dir, name, _) = paramStr(1).splitFile
  let path = dir / name
  if execCmd("nim nir " & path) != 0:
    raise newException(CatchableError, "NIR generation error")
  
  let nirFile = nimCache / (name & "_d") / (name & ".nir")
  if execCmd("nim c -r Nim/compiler/nir/nirc view " & nirFile) != 0:
    raise newException(CatchableError, "NIR rendering error")

  var c = GeneratorCtx(m: load(nirFile), lit: Literals())
  var s = ""
  c.findLabels c.m.code
  c.gen c.m.code
  render(c.tree, s, c.lit)
  echo nirFile
  echo "\nGenerated: "
  echo s

  echo "\nDet's:"
  for sym, det in c.dets:
    var s = ""
    render(det, s, c.lit)
    echo "block:"
    # if sym.nirSymId in c.m.symnames: 
    let name = c.m.symnames[sym.nirSymId]
    if hasLitId(c.m.lit.strings, name):
      echo "  NIR sym: ", c.m.lit.strings[name]
    echo "  SYM: ", sym
    echo "  DET:  \n", indent(s, 4)

  # Test z3 generation
  import z3gen {.all.}
  import z3/z3_api
  let cfg = Z3_mk_config()
  Z3_set_param_value(cfg, "model", "true")
  
  Z3_set_param_value(cfg, "well_sorted_check", "true")
  Z3_set_param_value(cfg, "trace", "true")
  
  var z = Z3Gen(z3: Z3_mk_context(cfg), lit: c.lit)
  z.types = initTypeGraph(Literals())
  Z3_set_error_handler(z.z3, onErr)
  Z3_set_ast_print_mode(z.z3, Z3_PRINT_SMTLIB_COMPLIANT)
  gen(z, c.tree)
