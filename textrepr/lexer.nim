import ../smtir
import std/lexbase

type
  TokenKind* = distinct byte

proc `==`*(a, b: TokenKind): bool {.borrow.}
proc keyword*(k: NodeKind): TokenKind = TokenKind(k.byte)

const
  lastKeyword* = byte NodeKind.high
  lvalueKeywords* = {
    keyword SymAsgn, 
    keyword Coupled, 
    keyword Checked
  }

  Eof* = TokenKind(lastKeyword + 1)
  Newline* = TokenKind(lastKeyword + 2)
  Invalid* = TokenKind(lastKeyword + 3)
  CurlyLe* = TokenKind(lastKeyword + 4)
  CurlyRi* = TokenKind(lastKeyword + 5)
  Number* = TokenKind(lastKeyword + 6)
  Ident* = TokenKind(lastKeyword + 7)

  # sugar: ==, <, <=, >=, >, =
  Eq* = TokenKind(lastKeyword + 8)
  Lt* = TokenKind(lastKeyword + 9)
  Le* = TokenKind(lastKeyword + 10)
  Gt* = TokenKind(lastKeyword + 11)
  Ge* = TokenKind(lastKeyword + 12)
  Asgn* = TokenKind(lastKeyword + 13)

  LPar* = TokenKind(lastKeyword + 14)
  RPar* = TokenKind(lastKeyword + 15)

proc `$`*(k: TokenKind): string =
  if k.byte <= lastKeyword: $NodeKind(k)
  else:
    case k
    of Eof: "[Eof]"
    of NewLine: "[NewLine]"
    of Invalid: "[Invalid]"
    of CurlyLe: "[CurlyLe]"
    of CurlyRi: "[CurlyRi]"
    of Number: "[Number]"
    of Ident: "[Ident]"
    of Eq: "[==]"
    of Lt: "[<]"
    of Le: "[<=]"
    of Gt: "[>]"
    of Ge: "[>=]"
    of Asgn: "[=]"
    of LPar: "[(]"
    of RPar: "[)]"
    else: ""

type
  Lexer* = object of BaseLexer
  Token* = object
    kind*: TokenKind
    s*: string
  
  TokensData* = object
    kind*: seq[TokenKind]
    s*: seq[string]

proc getNumber(L: var Lexer, tok: var Token) =
  var
    pos = L.bufpos
    buf = L.buf

  while buf[pos] in {'0'..'9', '_', 'a'..'z', 'A'..'Z'}:
    add(tok.s, buf[pos])
    inc pos
  
  tok.kind = Number

proc b(a, b: char): int =
  (1 shl a.int) or b.int

proc getPunctuator(L: var Lexer, tok: var Token) =
  let 
    pos = L.bufpos

    a = L.buf[pos]
    b = L.buf[pos + 1]
  
  tok.kind =
    case b(a, b)
    of b('=','='): Eq
    of b('<','='): Le
    of b('>','='): Ge
    else:
      case a
      of '=': Asgn
      of '<': Lt
      of '>': Gt
      else: Invalid
  
  add(tok.s, a)
  if tok.kind in {Eq, Le, Ge}: add(tok.s, b)

const
  CR* = '\x0D'
  LF* = '\x0A'

proc handleCRLF(L: var Lexer, pos: int): int =
  case L.buf[pos]
  of CR: result = handleCR(L, pos)
  of LF: result = handleLF(L, pos)
  else: result = pos

proc skip(L: var Lexer, tok: var Token) =
  var
    pos = L.bufpos
    buf = L.buf

  while true:
    case buf[pos]
    of ' ': inc pos
    of CR, LF:
      pos = handleCRLF(L, pos)
      buf = L.buf
      tok.kind = Newline
    else: break
  
  L.bufpos = pos

import std/[sugar, macros]
macro genKeywordCase(val: string, elseKind: uint32): untyped =
  result = newNimNode(nnkCaseStmt)
  result.add(val)
  for kw in NodeKind:
    var branch = newNimNode(nnkOfBranch).add(
      newLit($kw),
      newLit(kw.uint32)
    )
    result.add branch
  result.add newNimNode(nnkElse).add(elseKind)

const
  keywordChars = {'a'..'z', 'A'..'Z', '_'}

proc getKeywordOrIdent(L: var Lexer, tok: var Token) =
  const mxLen = max(
    collect do: 
      for i in NodeKind:
        len($i)
  )
  const defaultKind = Ident
  var
    pos = L.bufpos
    buf = L.buf
    kind = defaultKind

  while true:
    if buf[pos] notin keywordChars: break
    add(tok.s, buf[pos])
    if len(tok.s) > mxLen:
      break

    kind = TokenKind genKeywordCase(tok.s, kind.uint32)
    inc pos
  
  tok.kind = kind
  if kind.byte <= lastKeyword:
    let len = len($NodeKind(tok.kind))
    setLen(tok.s, len)

proc eat(L: var Lexer, tok: Token) =
  # inc pos by s len
  inc(L.bufpos, len(tok.s))

proc getTok*(L: var Lexer, tok: var Token) =
  skip(L, tok)
  if tok.kind == Newline: return
  
  case L.buf[L.bufpos]
  of '0':
    if L.buf[L.bufpos + 1] in '1'..'9':
      raiseAssert "Leading zero..."
    # else:

  of '1'..'9': getNumber(L, tok)
  of '=', '<', '>': getPunctuator(L, tok)
  of '{':
    inc(L.bufpos)
    tok.kind = CurlyLe
  of '}':
    inc(L.bufpos)
    tok.kind = CurlyRi
  of {'a'..'z', 'A'..'Z'}: getKeywordOrIdent(L, tok)
  of EndOfFile:
    tok.kind = Eof
  else: discard
  L.eat(tok)

# iterator tokenize(s: var Lexer): Token =
# TODO: add strval

iterator tokenize*(L: var Lexer): Token =
  var tok = Token()
  while tok.kind != Eof:
    tok = Token()
    getTok(L, tok)
    if tok.kind == Eof: break
    yield tok
  
when isMainModule:
  var L = Lexer()
  import std/streams
  var strm = newStringStream("""
  Peta = y
  """)
  L.open(strm)
  for i in tokenize(L):
    echo i