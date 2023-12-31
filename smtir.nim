type
  ValueType* = enum
    Bool
    Int
    Float
    Rational #Q

    String
    Set

    Seq
    Array

  NodeKind* = enum
    None
    ImmediateVal
    Typed

    Scalar # {ValueType, ImmediateVal+ | None}
    Vector # {Scalar, ImmediateVal}

    SymAsgn # {ImmediateVal, Scalar | Vector}
    SymUse
    ExternalSymUse

    Conv # {Typed, Typed, SymUse | Scalar} # A -> B 
    Coupled # {ExternalSymUse, ImmediateVal+} useful in simplifier
    Range # {ImmediateVal | None, ImmediateVal | None}

    Concat # {(SymUse | BitVec)+}
    Extract # {Range, SymUse | BitVec}

    # SAT theory
    And
    Or
    Not
    
    # Arithmetic
    Add
    Sub
    Mul
    Div
    Mod

    # BitVec
    BitShl
    BitShr
    BitAnd
    BitOr
    BitXor
    BitNot

import Nim/compiler/nir/[nirlineinfos, nirinsts]

type
  Node* = object
    x: uint32
    info: PackedLineInfo # I don't know it will works or not ?

const
  LastVectorType {.used.} = Rational
  LastAtomicValue {.used.} = Typed
  OpcodeBits = 8'u32
  OpcodeMask = (1'u32 shl OpcodeBits) - 1'u32

template kind*(n: Node): NodeKind = NodeKind(n.x and OpcodeMask)
template operand*(n: Node): uint32 = (n.x shr OpcodeBits)

template toX*(k: NodeKind; operand: uint32): uint32 =
  uint32(k) or (operand shl OpcodeBits)



type
  Tree* = object
    nodes: seq[Node]
    

proc prepare*(tree: var Tree; info: PackedLineInfo; kind: NodeKind): PatchPos =
  result = PatchPos tree.nodes.len
  tree.nodes.add Node(x: toX(kind, 1'u32), info: info)

proc patch*(tree: var Tree; pos: PatchPos) =
  let pos = pos.int
  let k = tree.nodes[pos].kind
  assert k > LastAtomicValue
  let distance = int32(tree.nodes.len - pos)
  assert distance > 0
  tree.nodes[pos].x = toX(k, cast[uint32](distance))

template build*(tree: var Tree; info: PackedLineInfo; kind: NodeKind; body: untyped) =
  let pos = prepare(tree, info, kind)
  body
  patch(tree, pos)

proc addSymUse*(t: var Tree; info: PackedLineInfo; s: SymId) {.inline.} =
  t.nodes.add Node(x: toX(SymUse, uint32(s)), info: info)

proc addImmediateVal*(t: var Tree; info: PackedLineInfo; x: int) =
  assert x >= 0 and x < ((1 shl 32) - OpcodeBits.int)
  t.nodes.add Node(x: toX(ImmediateVal, uint32(x)), info: info)

proc immediateVal*(ins: Node): int {.inline.} =
  assert ins.kind == ImmediateVal
  result = cast[int](ins.operand)

template `[]`*(t: Tree; n: NodePos): Node = t.nodes[n.int]


template rawSpan(n: Node): int = int(operand(n))
proc len*(tree: Tree): int {.inline.} = tree.nodes.len

proc nextChild(tree: Tree; pos: var int) {.inline.} =
  if tree.nodes[pos].kind > LastAtomicValue:
    assert tree.nodes[pos].operand > 0'u32
    inc pos, tree.nodes[pos].rawSpan
  else:
    inc pos

proc next*(tree: Tree; pos: var NodePos) {.inline.} = nextChild tree, int(pos)

template firstSon*(n: NodePos): NodePos = NodePos(n.int+1)

template skipTyped*(n: NodePos): NodePos = NodePos(n.int+2)

iterator sons*(tree: Tree; n: NodePos): NodePos =
  var pos = n.int
  assert tree.nodes[pos].kind > LastAtomicValue
  let last = pos + tree.nodes[pos].rawSpan
  inc pos
  while pos < last:
    yield NodePos pos
    nextChild tree, pos


proc render*(t: Tree; n: NodePos; s: var string; nesting = 0) =
  for _ in 0..<nesting: s.add "  "
  case t[n].kind:
  of ImmediateVal: s.add($t[n].immediateVal)
  else:
    s.add $t[n].kind
    s.add " {\n"
    for i in sons(t, n):
      render(t, i, s, nesting + 1)
      s.add "\n"
    
    for i in 0..<nesting: s.add "  "
    s.add "}"

proc render*(t: Tree; s: var string) =
  var i = 0
  while i < t.len:
    render t, NodePos i, s
    nextChild t, i
