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
    CheckTypeValWaitIdent

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
template pos: auto = p.tokPos
template tokKind: untyped = tok.kind[pos]
template tokS: untyped = tok.s[pos]

# proc build(p: var Parser, tok: TokensData)
import ../packed_syms
proc buildSimpleExpr(p: var Parser, tok: TokensData) =
  var info = PackedLineInfo.default
  case tokKind
  of keyword(IntVal):
    p.st = IntValWaitNumber
  of keyword(ImmediateVal):
    p.st = ImmediateWaitNumber
  of keyword(Typed):
    p.st = TypedWaitNumber
  of keyword(CheckTypeVal):
    p.st = CheckTypeValWaitIdent
  of NewLine: discard
  of Number:
    var val: int
    if parseInt(tokS, val) != len(tokS):
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
    
    p.st = Nop
  of Ident:
    case p.st
    of CheckTypeValWaitIdent:
      let typ: CheckType =
        case tokS
        of "Range": Range
        of "Index": Index
        of "Overflow": Overflow
        of "Assert": Assert
        of "Refinement": Refinement
        else:
          raiseAssert "CheckType should be in {Range, Index, Overflow, Assert, Refinement}"
      
      p.t.addCheckType info, typ
      p.st = Nop
    else:
      if tokS notin p.syms:
        p.syms[tokS] = SymId(p.symId)
        p.lastId = SymId(p.symId)
        inc p.symId

      p.t.addSymUse info, toPacked(p.syms[tokS], uint16 p.symsCnt[p.syms[tokS]])
  of LPar:
    raiseAssert "Unsupported"
  of CurlyLe:
    inc pos # {
    while tok.kind[pos] != CurlyRi:
      buildSimpleExpr(p, tok)

  elif tokKind.byte <= lastKeyword:
    if tokKind == keyword(Phi): p.symKind = Phi
    build p.t, info, NodeKind(tokKind):
      inc pos # Node -> CurlyLe
      buildSimpleExpr(p, tok)
  
  else:
    raiseAssert "Inexpected token with kind:  " & $tokKind

  inc pos

proc parseExprStmt(p: var Parser, tok: TokensData) =
  # (Node {}) | (Ident = Node {})
  var info = PackedLineInfo.default
  let nextTok = p.tokPos + 1
  if tok.kind[nextTok] == Asgn:
    build p.t, info, SymAsgn:
      buildSimpleExpr(p, tok) # Ident -> Asgn
      
      p.t.reservePos(info, reserved)
      inc pos # Asgn -> Node
      buildSimpleExpr(p, tok)

      p.t.addSymKind info, p.symKind
      # inc(p.symsCnt, p.lastId)
      p.t.updateReserve(reserved)
  else:
    buildSimpleExpr(p, tok)

proc parse*(p: var Parser, tok: TokensData) =
  while p.tokPos < len(tok.s) - 1:
    parseExprStmt(p, tok)

when isMainModule:
  var p = Parser()
  var L = Lexer()
  import std/streams
  import std/lexbase

  var strm = newStringStream("""
  a = Scalar {
    Typed 3
    IntVal 1
  }
  Checked {
    ImmediateVal 0
    CheckTypeVal Assert
    Le {
      a
      IntVal 5
    }
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