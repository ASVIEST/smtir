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

    SymAsgn
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

  Node* = object
    x: uint32

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

