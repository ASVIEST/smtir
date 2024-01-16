## this module produces SMTIr code from NIR
import Nim/compiler/nir/nirinsts except build
import Nim/compiler/nir/nirfiles
import Nim/compiler/ic/bitabs
import smtir
import irtypes
import std/tables
import std/math
import packed_syms
import Nim/compiler/nir/nirtypes except Literals

type
  GeneratorCtx = object
    m: NirModule
    tree: smtir.Tree
    lit: Literals
    symModifies: CountTable[SymId] # NIR is not SSA. 
                                   # every modification increase it
                                   # and used for making new SMTIR sym

    stack: seq[smtir.Tree] # lvalues stack, need to say that will be after 
                           # current lvalue from rvalue

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

template withNextSym(s, body): untyped =
  c.symModifies.inc s
  body
  c.symModifies.inc s, -1

template withOldSym(s, body): untyped =
  c.symModifies.inc s, -1
  body
  c.symModifies.inc s

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
      
      withNextSym t[s].symId:
        tree.addSymUse info, c.packedSymId(t[s].symId)
      
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
      
      withNextSym t[s].symId:
        tree.addSymUse info, c.packedSymId(t[s].symId)


proc genDefaultVal(c: var GeneratorCtx; types: nirtypes.TypeGraph; lit: nirtypes.Literals; t: nirtypes.TypeId; info: PackedLineInfo) =
  # adds a default scalar for type
  c.tree.build info, Scalar: # arrays currently not supported
    genType c, c.tree, types, lit, t, info
    case types[t].kind
    of IntTy, UintTy, BoolTy, CharTy, FloatTy:
      c.tree.addIntVal c.lit.numbers, info, 0
    else: raiseAssert "can't get default val"

proc packedSymId(c: GeneratorCtx; s: SymId): PackedSymId =
  toPacked(s, uint16 c.symModifies[s])

proc addLValues(c: var GeneratorCtx) =
  for i in c.stack:
    copyTree(c.tree, i)
  c.stack = @[]

proc gen(c: var GeneratorCtx, t: nirinsts.Tree, n: NodePos) =
  let info = t[n].info
  case t[n].kind
  of SymUse:
    let s = t[n].symId
    c.tree.addSymUse info, c.packedSymId(s)
  of SummonGlobal, Summon:
    let (typ, def) = sons2(t, n)
    c.tree.build info, SymAsgn:
      gen(c, t, def) # update modifiers counter
      genDefaultVal c, c.m.types, c.m.lit, t[typ].typeId, info
  of SymDef:
    let s = t[n].symId
    c.symModifies.inc s
    c.tree.addSymUse info, c.packedSymId(s)
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
    c.symModifies.inc s
    c.tree.build info, SymAsgn:
      c.gen(t, le) # This symId is modified by old symId, so current symId and oldSym id is same symId
      withOldSym s:
        c.gen(t, ri)
    c.addLValues

  of IntVal: c.tree.addIntVal(c.lit.numbers, info, c.m.lit.numbers[t[n].litId])
  
  of CheckedAdd: checkedBinOp(Add)
  of CheckedDiv: checkedBinOp(Div)
  of CheckedMod: checkedBinOp(Mod)
  of CheckedMul: checkedBinOp(Mul)

  of CheckedGoto, Goto: discard
  # of SelectValue:

  # of SelectPair:
  #   let (le, ri) = sons2(t, n)
  #   gen(c, t, le) # gen select value

  # of Select:
  #   let (typ, selector) = sons2(t, n)
  #   for ch in sonsFromN(t, n, 2):
  #     assert t[ch].kind == SelectPair
    
  of Label: discard "skip label"
  else:
    raiseAssert $t[n].kind & " is not supported"

proc gen(c: var GeneratorCtx, t: nirinsts.Tree) =
  var i = NodePos(0)
  while i.int < t.len:
    gen c, t, i
    next t, i

when isMainModule:
  import std/[os, osproc]
  import std/compilesettings
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
  c.gen c.m.code
  render(c.tree, s, c.lit)
  echo nirFile
  echo "\nGenerated: "
  echo s

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
