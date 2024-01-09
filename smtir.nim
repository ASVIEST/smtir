import irtypes
import Nim/compiler/ic/bitabs
import packed_syms

type
  CheckType* = enum
    Range
    Index
    Overflow
    Assert
    Refinement

  NodeKind* = enum
    None
    ImmediateVal
    IntVal
    Typed
    CheckTypeVal

    ExternalSymUse

    SymUse
    SymAsgn # {ImmediateVal, Scalar | Vector | (Add | Sub | Div | Mul | Mod)}

    Scalar # {ValueType, ImmediateVal+ | None}
    Vector # {Scalar, ImmediateVal}

    

    Conv # {Typed #[new type]#, Typed #[old type]#, SymUse | Scalar} # B -> A 
    Coupled # {ExternalSymUse, ImmediateVal+} useful in simplifier
    Range # {ImmediateVal | None, ImmediateVal | None}

    Concat # {(SymUse | BitVec)+}
    Extract # {Range, SymUse | BitVec}
    
    Constraint
    Eq
    Le
    Lt

    Checked # {ImmediateVal #[isFact]#, CheckType, Constraint+}
    Phi # {Typed, (SymUse | Det)*}
    Det # {And | Or | Not | SymUse #[Cond]#, SymUse}
    ResolvedPhi # {SymUse, SymUse* #[Params]#}

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
  LastAtomicValue {.used.} = SymUse
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

proc addSymUse*(t: var Tree; info: PackedLineInfo; s: PackedSymId) {.inline.} =
  t.nodes.add Node(x: toX(SymUse, uint32(s)), info: info)

proc symId*(ins: Node): PackedSymId {.inline.} =
  assert ins.kind == SymUse
  PackedSymId(ins.operand)

proc addTyped*(t: var Tree; info: PackedLineInfo; typ: TypeId) {.inline.} =
  assert typ.int >= 0
  t.nodes.add Node(x: toX(Typed, cast[uint32](typ)), info: info)

proc addNone*(t: var Tree; info: PackedLineInfo) {.inline.} =
  t.nodes.add Node(x: toX(None, 0'u32), info: info)

proc addImmediateVal*(t: var Tree; info: PackedLineInfo; x: int) =
  assert x >= 0 and x < ((1 shl 32) - OpcodeBits.int)
  t.nodes.add Node(x: toX(ImmediateVal, uint32(x)), info: info)

proc addIntVal*(t: var Tree; integers: var BiTable[int64]; info: PackedLineInfo; x: int64) =
  t.nodes.add Node(x: toX(IntVal, uint32(integers.getOrIncl(x))), info: info)

proc addCheckType*(t: var Tree; info: PackedLineInfo; x: CheckType) =
  t.nodes.add Node(x: toX(CheckTypeVal, cast[uint32](x)), info: info)

proc immediateVal*(n: Node): int {.inline.} =
  assert n.kind == ImmediateVal
  result = cast[int](n.operand)

proc checkTypeVal*(n: Node): CheckType =
  assert n.kind == CheckTypeVal
  cast[CheckType](n.operand)

proc typeId*(n: Node): TypeId =
  assert n.kind == Typed
  cast[TypeId](n.operand)

proc litId*(n: Node): LitId {.inline.} =
  assert n.kind == IntVal
  LitId n.operand

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

iterator sons*(tree: Tree; n: NodePos): NodePos =
  var pos = n.int
  assert tree.nodes[pos].kind > LastAtomicValue
  let last = pos + tree.nodes[pos].rawSpan
  inc pos
  while pos < last:
    yield NodePos pos
    nextChild tree, pos

proc isAtom(tree: Tree; pos: NodePos): bool {.inline.} = tree.nodes[pos.int].kind <= LastAtomicValue

proc span(tree: Tree; pos: int): int {.inline.} =
  if tree.nodes[pos].kind <= LastAtomicValue: 1 else: int(tree.nodes[pos].operand)

proc sons2*(tree: Tree; n: NodePos): (NodePos, NodePos) {.inline.} =
  assert(not isAtom(tree, n))
  let a = n.int+1
  let b = a + span(tree, a)
  result = (NodePos a, NodePos b)

proc sons3*(tree: Tree; n: NodePos): (NodePos, NodePos, NodePos) {.inline.} =
  assert(not isAtom(tree, n))
  let a = n.int+1
  let b = a + span(tree, a)
  let c = b + span(tree, b)
  result = (NodePos a, NodePos b, NodePos c)

iterator sonsFromN*(tree: Tree; n: NodePos; toSkip = 2): NodePos =
  var pos = n.int
  assert tree.nodes[pos].kind > LastAtomicValue
  let last = pos + tree.nodes[pos].rawSpan
  inc pos
  for i in 1..toSkip:
    nextChild tree, pos
  while pos < last:
    yield NodePos pos
    nextChild tree, pos

proc rangeBounds*(t: Tree, n: NodePos): Slice[uint32] =
  let (le, ri) = sons2(t,n)
  t[le].operand .. t[ri].operand

proc render*(t: Tree; n: NodePos; s: var string; lit: Literals; nesting = 0) =
  for _ in 0..<nesting: s.add "  "
  case t[n].kind:
  of None: s.add "None"
  of ImmediateVal:
    s.add "ImmediateVal "
    s.add $t[n].immediateVal
  of IntVal:
    s.add "IntVal "
    s.add $lit.numbers[t[n].litId]
  of SymUse:
    s.add "SymUse "
    s.add $(PackedSymId t[n].operand)
  of Typed:
    s.add '<' & $t[n].operand & '>'
  of CheckTypeVal:
    s.add "CheckTypeVal "
    s.add $t[n].checkTypeVal
  else:
    s.add $t[n].kind
    s.add " {\n"
    for i in sons(t, n):
      render(t, i, s, lit, nesting + 1)
      s.add "\n"
    
    for i in 0..<nesting: s.add "  "
    s.add "}"

proc render*(t: Tree; s: var string; lit: Literals) =
  var i = 0
  while i < t.len:
    render t, NodePos i, s, lit
    s.add '\n'
    nextChild t, i
