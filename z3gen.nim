import smtir
import Nim/compiler/nir/nirlineinfos
import Nim/compiler/nir/nirinsts except Tree
import std/tables
{.experimental: "strictDefs".}
{.experimental: "strictFuncs".}

import z3/z3_api
type
  Z3Gen = object
    z3: Z3_context
    ast: Z3_ast

    facts: seq[Z3_ast]
    # strings*: BiTable[string]
    syms*: Table[SymId, Z3_ast]

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

template mk_var(name: string, ty: Z3_sort): Z3_ast =
  let sym = Z3_mk_string_symbol(c.z3, name)
  Z3_mk_const(c.z3, sym, ty)

func getSort(c: var Z3Gen; typ: ValueType): Z3_sort =
  case typ
  of Int: Z3_mk_int_sort(c.z3)
  of Rational: Z3_mk_real_sort(c.z3)
  of Bool: Z3_mk_bool_sort(c.z3)
  else: raiseAssert"unsupported"

func genRValue(c: var Z3Gen; t: Tree, n: NodePos): Z3_ast =
  case t[n].kind
  of Eq: binOp(Z3_mk_eq)
  of Le: binOp(Z3_mk_le)
  of Lt: binOp(Z3_mk_lt)
  of And: binOp(Z3_mk_and, true)
  of SymUse:
    c.syms[t[n].symId]
  of Scalar:
    let (typRaw, val) = sons2(t, n)
    let typ = cast[ValueType](t[typRaw].operand)
    let sort = c.getSort(typ)
    if t[val].kind == None: mk_var("SCALAR", sort)
    else:
      assert t[val].kind == ImmediateVal
      let v = t[val].operand

      case typ
      of Int: Z3_mk_int64(c.z3, cast[clonglong](v), sort)
      of Rational:
        # TODO: fix
        type Real = object
          num: cint
          den: cint

        let real = cast[Real](v)
        Z3_mk_real(c.z3, real.num, real.den)
      of Bool:
        if v == 1: Z3_mk_true(c.z3)
        elif v == 0: Z3_mk_false(c.z3)
        else: raiseAssert "Bool must be 0 | 1"
      of Float: Z3_mk_fpa_numeral_double(c.z3, cast[cdouble](v), sort)
      else: raiseAssert "Invalid"
  of Add: binOp(Z3_mk_add, true)
  of Sub: binOp(Z3_mk_sub, true)
  of Div: binOp(Z3_mk_div)
  of Mul: binOp(Z3_mk_mul, true)
  of Mod: binOp(Z3_mk_mod)
  else:
    raiseAssert "never"



proc toString*(c: Z3_context; v: Z3_ast): string =
  ## Create a string representation of the Z3 ast node
  {.push hint[ConvFromXtoItselfNotNeeded]: off.}
  $Z3_ast_to_string(c, v.Z3_ast)


proc genLValue(c: var Z3Gen; t: Tree; n: NodePos) =
  case t[n].kind
  of SymAsgn:
    let (le, ri) = sons2(t, n)
    c.syms[t[le].symId] = c.genRValue(t, ri)

  of Check:
    # check node and maybe make modify tree and make it fact
    let (isFact, typ) = sons2(t, n)

    var constraints: seq[Z3_ast] = @[]
    for ch in sonsFromN(t, n, 2):
      constraints.add genRValue(c, t, ch)
    
    let question: Z3_ast
    if t[isFact].operand == 0:
      question = Z3_mk_and(c.z3, cuint constraints.len, constraints[0].addr)
      echo toString(c.z3, question)
    else:
      question = Z3_ast.default
    
    discard typ

  else:
    raiseAssert "Invalid lvalue: " & $t[n].kind

proc gen(c: var Z3Gen; t: Tree) =
  var i = NodePos 0
  while i.int < t.len:
    genLValue c, t, i
    next t, i

when isMainModule:
  var t = Tree()
  let info = PackedLineInfo.default

  t.build info, SymAsgn:
    t.addSymUse info, SymId 0
    t.build info, Scalar:
      t.addTyped info, Int
      t.addImmediateVal info, 1
      # t.addNone info
  
  t.build info, SymAsgn:
    t.addSymUse info, SymId 42 # SymId 42 is result

    t.build info, Add:
      t.addSymUse info, SymId 0
      t.build info, Scalar:
        t.addTyped info, Int
        t.addImmediateVal info, 4
  
  t.build info, Check:
    t.addImmediateVal info, 0
    t.addNone info # it not used for now
    t.build info, And:
      t.build info, Lt:
        t.addSymUse info, SymId 42
        t.build info, Scalar:
          t.addTyped info, Int
          t.addImmediateVal info, 6
      
      t.build info, Le:
        t.build info, Scalar:
          t.addTyped info, Int
          t.addImmediateVal info, 1
        t.addSymUse info, SymId 42

  var s = ""
  render(t, s)
  echo s

  let cfg = Z3_mk_config()
  Z3_set_param_value(cfg, "model", "true")
  var c = Z3Gen(z3: Z3_mk_context(cfg))
  gen(c, t)
  echo toString(c.z3, c.syms[SymId 42])
