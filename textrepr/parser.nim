import lexer
import ../smtir
import std/parseutils
import ../Nim/compiler/ic/bitabs
import ../Nim/compiler/nir/nirlineinfos
from ../Nim/compiler/nir/nirinsts import SymId, `==`

import std/tables
import ../irtypes

type
  State = enum
    Nop
    IntValWaitNumber
    ImmediateWaitNumber
    TypedWaitNumber

  Parser* = object
    t*: Tree
    st: State
    strings*: BiTable[string]
    numbers*: BiTable[int64]
    tokPos: int

    symKind: SymKind
    symsCnt: CountTable[SymId]
    syms: Table[string, SymId]
    symId: int
    lastId: SymId


import std/hashes
template tokKind: untyped = tok.kind[pos]
template tokS: untyped = tok.s[pos]

proc build(p: var Parser, tok: TokensData, pos: int = p.tokPos)
import ../packed_syms
proc buildSimpleExpr(p: var Parser, tok: TokensData, pos: int = p.tokPos) =
  var info = PackedLineInfo.default
  case tokKind
  of keyword(IntVal):
    p.st = IntValWaitNumber
  of keyword(ImmediateVal):
    p.st = ImmediateWaitNumber
  of keyword(Typed):
    p.st = TypedWaitNumber

  of Number:
    var val: int
    if parseInt(tokS, val) != len(tokS):
      # p.t.addError(errInvalidNumber, tok.s)
      raiseAssert "Invalid number:  " & tokS
    
    case p.st
    of IntValWaitNumber:
      p.t.addIntVal p.numbers, info, val
    of ImmediateWaitNumber:
      p.t.addImmediateVal info, val
    of TypedWaitNumber:
      p.t.addTyped info, TypeId(val)
    else:
      raiseAssert "Use {IntVal, ImmediateVal, Typed} before number"
  of Ident:
    if tokS notin p.syms:
      p.syms[tokS] = SymId(p.symId)
      p.lastId = SymId(p.symId)
      inc p.symId

    p.t.addSymUse info, toPacked(p.syms[tokS], uint16 p.symsCnt[p.syms[tokS]])
  of LPar:
    raiseAssert "Unsupported"
    # buildExpr(p, tok)
    # if p
  of CurlyLe:
    inc p.tokPos # {
    while tok.kind[p.tokPos] != CurlyRi:
      buildSimpleExpr(p, tok)

  elif tokKind.byte <= lastKeyword:
    if tokKind == keyword(Phi): p.symKind = Phi

    inc p.tokPos
    build p.t, info, NodeKind(tokKind):
      buildSimpleExpr(p, tok)
  else:
    # echo "heh"
    # inc p.tokPos
    # build(p, tok)
    discard

  inc p.tokPos

proc build(p: var Parser, tok: TokensData, pos: int = p.tokPos) =
  ## expr: asgn
  ## asgn: ident = rval

  var info = PackedLineInfo.default
  case tokKind
  of Newline: discard
  of Asgn:
    let (l, r) = (p.tokPos - 1, p.tokPos + 1)
    build p.t, info, SymAsgn:
      buildSimpleExpr(p, tok, l)
      inc(p.symsCnt, p.lastId)
      p.t.reservePos(info, reserved)
      buildSimpleExpr(p, tok, r)

      p.t.addSymKind info, p.symKind
      p.t.updateReserve(reserved)
  
  of lvalueKeywords:
    buildSimpleExpr(p, tok)

  else: discard
  #   buildSimpleExpr(p, tok)
  inc p.tokPos

proc parse*(p: var Parser, tok: TokensData) =
  while p.tokPos < len(tok.s):
    build(p, tok)

when isMainModule:
  var p = Parser()
  var L = Lexer()
  import std/streams
  import std/lexbase

  var strm = newStringStream("""
  a = Phi {
    IntVal 1
    Scalar {
      IntVal 5
    }
    IntVal 3
  }
  """)
  L.open(strm)
  var data = TokensData()
  # data.fill(L)

  for tok in tokenize(L):
    echo tok
    data.s.add tok.s
    data.kind.add tok.kind
  
  parse(p, data)

  var s = ""
  render(p.t, s, p.numbers, p.strings)
  echo s