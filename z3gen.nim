import smtir, irtypes
import Nim/compiler/nir/nirlineinfos
import Nim/compiler/nir/nirinsts except Tree # need PackedSymId and NodePos
import Nim/compiler/ic/bitabs

import std/tables
import packed_syms
{.experimental: "strictDefs".}
{.experimental: "strictFuncs".}
# TODO: {.experimental: "strictNotNil".}

import z3/z3_api
type
  Z3Gen = object
    z3*: Z3_context
    ast: Z3_ast

    facts: seq[Z3_ast]
    # strings*: BiTable[string]
    syms*: Table[PackedSymId, Z3_ast]
    types*: TypeGraph
    lit*: Literals
  
  Z3Exception = object of ValueError

template binOp(op; needList: static bool = false): untyped =
  let (a, b) = sons2(t, n)
  when not needList:
    op(
      c.z3,
      c.genRValue(t, a), 
      c.genRValue(t, b)
    )
  else:
    var args = [c.genRValue(t, a), c.genRValue(t, b)]
    op(
      c.z3, 2,
      args[0].addr
    )

template unaryOp(op): untyped =
  op(c.z3, c.genRValue(t, n.firstSon))

template mk_var(name: string, ty: Z3_sort): Z3_ast =
  let sym = Z3_mk_string_symbol(c.z3, name)
  Z3_mk_const(c.z3, sym, ty)

func getSort(c: var Z3Gen; types: TypeGraph, t: TypeId): Z3_sort =
  case types[t].kind
  of IntTy, UintTy: Z3_mk_int_sort(c.z3)
  of RationalTy: Z3_mk_real_sort(c.z3)
  of BoolTy: Z3_mk_bool_sort(c.z3)
  else: 
    debugEcho types[t].kind
    raiseAssert"unsupported"

proc genRValue(c: var Z3Gen; t: Tree, n: NodePos): Z3_ast =
  case t[n].kind
  of Not: unaryOp(Z3_mk_not)
  of Eq: binOp(Z3_mk_eq)
  of Le: binOp(Z3_mk_le)
  of Lt: binOp(Z3_mk_lt)
  of And: binOp(Z3_mk_and, true)
  of SymUse:
    c.syms[t[n].symId]
  of Scalar:
    let (typRaw, val) = sons2(t, n)
    let typ = cast[TypeId](t[typRaw].operand)
    let sort = c.getSort(c.types, typ)
    if t[val].kind == None: mk_var("SCALAR", sort)
    else:
      assert t[val].kind in {NodeKind.ImmediateVal, IntVal}
      let v =
        if t[val].kind == ImmediateVal: cast[int64](t[val].operand)
        else: c.lit.numbers[t[val].litId]

      case c.types[typ].kind
      of IntTy: Z3_mk_int64(c.z3, cast[clonglong](v), sort)
      of RationalTy:
        # TODO: fix
        type Real = object
          num: cint
          den: cint

        let real = cast[Real](v)
        Z3_mk_real(c.z3, real.num, real.den)
      of BoolTy:
        if v == 1: Z3_mk_true(c.z3)
        elif v == 0: Z3_mk_false(c.z3)
        else: raiseAssert "Bool must be 0 | 1"
      of FloatTy: Z3_mk_fpa_numeral_double(c.z3, cast[cdouble](v), sort)
      else: raiseAssert "Invalid"
  of Add: binOp(Z3_mk_add, true)
  of Sub: binOp(Z3_mk_sub, true)
  of Div: binOp(Z3_mk_div)
  of Mul: binOp(Z3_mk_mul, true)
  of Mod: binOp(Z3_mk_mod)
  
  of BitShl: binOp(Z3_mk_bvshl)
  of BitShr: binOp(Z3_mk_bvashr) #why need logical shr ?
  of BitAnd: binOp(Z3_mk_bvand)
  of BitOr: binOp(Z3_mk_bvor)
  of BitXor: binOp(Z3_mk_bvxor)
  of BitNot: unaryOp(Z3_mk_bvnot)

  of Conv:
    let (newTypRaw, oldTypRaw, valRaw) = sons3(t, n)
    let (newTyp, oldTyp) = (
      t[newTypRaw].typeId, 
      t[oldTypRaw].typeId
    )
    let val = c.genRValue(t, valRaw)

    # where my pattern matching ?
    if c.types[newTyp].kind == BitVecTy and c.types[oldTyp].kind in {IntTy, UintTy}:
      Z3_mk_int2bv(c.z3, cuint(c.types[oldTyp].integralBits), val)
    elif c.types[newTyp].kind == IntTy and c.types[oldTyp].kind == BitVecTy:
      Z3_mk_bv2int(c.z3, val, true)
    elif c.types[newTyp].kind == UintTy and c.types[oldTyp].kind == BitVecTy:
      Z3_mk_bv2int(c.z3, val, false)
    elif c.types[newTyp].kind in {IntTy, UintTy} and c.types[oldTyp].kind == BoolTy:
      # if val: 1 else: 0
      let sort = Z3_mk_int_sort(c.z3)
      Z3_mk_ite(c.z3, val, Z3_mk_int(c.z3, 1, sort), Z3_mk_int(c.z3, 0, sort))
    else:
      raiseAssert "Invalid conv"
  
  of Extract:
    let (rng, s) = sons2(t, n)
    let bounds = rangeBounds(t, rng)
    Z3_mk_extract(c.z3, bounds.a, bounds.b, c.genRValue(t, s))

  of Concat:
    let (le, ri) = sons2(t, n)
    Z3_mk_concat(c.z3, c.genRValue(t, le), c.genRValue(t, ri))
  
  of Phi:
    # we could not analyze these Phi nodes for some patterns. 
    # Therefore, the SMT solver has to infer the Phi nodes by itself.

    # Generated ast is just if calls
    # for example:
    # y_2 = Phi {
    #   <Int>
    #   SymUse i # param

    #   Det {
    #     i < i_min
    #     y_0
    #   }
    #   Det {
    #     i >= i_min
    #     y_1
    #   }
    # }
    # -->
    # y_3 = const
    # If(i < i_min, y_3 == y_0, y_3 == y_1)
    # -> y_3

    let typ = cast[TypeId](t[n.firstSon].operand)
    var node = mk_var("PHI", c.getSort(c.types, typ))
    var condTree = Z3_mk_false(c.z3)
    for ch in sons(t, n):
      if t[ch].kind == Det:
        let (cond, val) = sons2(t, ch)
        condTree = Z3_mk_ite(
          c.z3,
          c.genRValue(t, cond),
          Z3_mk_eq(c.z3, node, c.genRValue(t, val)), # y_3 == y_0
          condTree
        )
    c.facts.add condTree
    node
  else:
    echo t[n].kind
    raiseAssert "never"



proc toString*(c: Z3_context; v: Z3_ast): string =
  ## Create a string representation of the Z3 ast node
  {.push hint[ConvFromXtoItselfNotNeeded]: off.}
  $Z3_ast_to_string(c, v.Z3_ast)

proc proveExpr(
  c: Z3Gen; 
  constraints: seq[Z3_ast],
  facts: seq[Z3_ast]
): Z3_ast =
  # not(facts -> question)
  # not(not facts or question)
  # facts and not question, if found solution, then it's invalid
  
  let question = Z3_mk_and(c.z3, cuint constraints.len, constraints[0].addr)
  let factsExpr =
    if facts.len > 0:
      Z3_mk_and(c.z3, cuint facts.len, facts[0].addr)
    else:
      Z3_mk_true(c.z3)

  var comb = [Z3_mk_not(c.z3, question), factsExpr]
  Z3_mk_and(c.z3, 2, addr(comb[0]))

type
  ProveResult = enum
    Unknown
    Proved
    UnProved

proc prove(
  c: Z3Gen;
  solver: var Z3_solver;
  constraints: seq[Z3_ast],
  facts: seq[Z3_ast]
): ProveResult =
  let toProve = proveExpr(
    c,
    constraints,
    c.facts
  )
  echo toString(c.z3, Z3_simplify(c.z3, toProve))
  Z3_solver_assert(c.z3, solver, toProve)
  let z3res = Z3_solver_check(c.z3, solver)
  
  case z3res
  of Z3_L_TRUE: Proved
  of Z3_L_FALSE: UnProved
  of Z3_L_UNDEF: Unknown

import strutils
proc genLValue(c: var Z3Gen; t: Tree; n: NodePos) =
  case t[n].kind
  of SymAsgn:
    let (le, ri) = sons2(t, n)
    c.syms[t[le].symId] = c.genRValue(t, ri)

  of Checked:
    # check node and maybe make modify tree and make it fact
    let (isFact, typ) = sons2(t, n)

    var constraints: seq[Z3_ast] = @[]
    for ch in sonsFromN(t, n, 2):
      constraints.add genRValue(c, t, ch)
    assert constraints.len > 0, "Checked node dont have constraints"

    if bool(t[isFact].operand): c.facts.add constraints
    else:
      var solver = Z3_mk_solver(c.z3)
      let proveResult = prove(
        c,
        solver,
        constraints,
        c.facts
      )
      if proveResult == Proved:
        let counterex = strip(
          $Z3_model_to_string(c.z3, Z3_solver_get_model(c.z3, solver))
        )
        if counterex.len > 0:
          raise newException(Z3Exception, $t[typ].checkTypeVal & " check falid. counter example:  " & counterex)
        else:
          raise newException(Z3Exception, $t[typ].checkTypeVal & " check failed")
      else: c.facts.add constraints
  else:
    raiseAssert "Invalid lvalue: " & $t[n].kind

proc gen(c: var Z3Gen; t: Tree) =
  var i = NodePos 0
  while i.int < t.len:
    genLValue c, t, i
    next t, i

proc onErr(ctx: Z3_context, e: Z3_error_code) {.nimcall.} =
  let msg = $Z3_get_error_msg(ctx, e)
  raise newException(Z3Exception, msg)

when isMainModule:
  var t = Tree()
  let info = PackedLineInfo.default
  var lit = Literals()

  # t.build info, SymAsgn:
  #   t.addSymUse info, PackedSymId 0
  #   t.build info, Scalar:
  #     t.addTyped info, Int32Id
  #     t.addIntVal lit.numbers, info, 1
  #     # t.addNone info
  
  # t.build info, SymAsgn:
  #   t.addSymUse info, PackedSymId 42 # SymId 42 is result

  #   t.build info, Add:
  #     t.addSymUse info, PackedSymId 0
  #     t.build info, Scalar:
  #       t.addTyped info, Int32Id
  #       t.addIntVal lit.numbers, info, 4
  
  # # SymId 0 = 1 + 4
  # # 1 <= SymId 0 < 6
  # t.build info, Checked:
  #   t.addImmediateVal info, 0
  #   t.addCheckType info, Range
  #   t.build info, And:
  #     t.build info, Lt:
  #       t.addSymUse info, PackedSymId 42
  #       t.build info, Scalar:
  #         t.addTyped info, Int32Id
  #         t.addIntVal lit.numbers, info, 6
      
  #     t.build info, Le:
  #       t.build info, Scalar:
  #         t.addTyped info, Int32Id
  #         t.addIntVal lit.numbers, info, 1
  #       t.addSymUse info, PackedSymId 42
  
  # t.build info, SymAsgn:
  #   t.addSymUse info, PackedSymId 43

  #   t.build info, Conv:
  #     t.addTyped info, BitVecId
  #     t.addTyped info, Int32Id
  #     t.addSymUse info, PackedSymId 42
  
  # Test Phi
  t.build info, SymAsgn:
    t.addSymUse info, PackedSymId 0
    t.build info, Scalar:
      t.addTyped info, Int32Id
      # t.addNone info
      t.addIntVal lit.numbers, info, 0
  
  t.build info, SymAsgn:
    t.addSymUse info, PackedSymId 99_0 # a
    t.build info, Scalar:
      t.addTyped info, Bool8Id
      t.addIntVal lit.numbers, info, 1
  
  t.build info, SymAsgn:
    t.addSymUse info, PackedSymId 99_1 # b
    t.build info, Scalar:
      t.addTyped info, Bool8Id
      t.addIntVal lit.numbers, info, 1
  
  t.build info, SymAsgn:
    t.addSymUse info, PackedSymId 1
    t.build info, Add:
      t.addSymUse info, PackedSymId 0
      t.build info, Scalar:
        t.addTyped info, Int32Id
        t.addIntVal lit.numbers, info, 1
  
  t.build info, SymAsgn:
    t.addSymUse info, PackedSymId 2
    t.build info, Add:
      t.addSymUse info, PackedSymId 0
      t.build info, Scalar:
        t.addTyped info, Int32Id
        t.addIntVal lit.numbers, info, 2
  
  t.build info, SymAsgn:
    t.addSymUse info, PackedSymId 42
    t.build info, Phi:
      t.addTyped info, Int32Id
      t.addSymUse info, PackedSymId 0
      t.build info, Det:
        t.addSymUse info, PackedSymId 99_0

        t.addSymUse info, PackedSymId 1
      
      t.build info, Det:
        t.build info, And:
          t.addSymUse info, PackedSymId 99_1
          t.build info, Not:
            t.addSymUse info, PackedSymId 99_0

        t.addSymUse info, PackedSymId 2
  
  t.build info, Checked:
    t.addImmediateVal info, 0
    t.addCheckType info, Range
    t.build info, Lt:
      t.build info, Scalar:
        t.addTyped info, Int32Id
        t.addIntVal lit.numbers, info, 1
      t.addSymUse info, PackedSymId 42

  var s = ""
  render(t, s, lit)
  echo s

  let cfg = Z3_mk_config()
  Z3_set_param_value(cfg, "model", "true")
  
  Z3_set_param_value(cfg, "well_sorted_check", "true")
  Z3_set_param_value(cfg, "trace", "true")
  
  var c = Z3Gen(z3: Z3_mk_context(cfg), lit: lit)
  c.types = initTypeGraph(Literals())
  Z3_set_error_handler(c.z3, onErr)
  Z3_set_ast_print_mode(c.z3, Z3_PRINT_SMTLIB_COMPLIANT)

  gen(c, t)
  # echo toString(c.z3, c.syms[PackedSymId 42])
  # echo toString(c.z3, c.syms[PackedSymId 43])
