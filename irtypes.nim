# simple type system, heavily inspired by nirtypes
# yes, type graph can be modified but usually this is not need,
# because sum types is not yet supported
import Nim/compiler/ic/bitabs

type
  TypeKind* = enum
    BoolTy
    IntTy
    UintTy # for example Z3_mk_bv2int, 
           # instead of making non atomic node, signed or unsigned 
           # it is a different atoms
    FloatTy
    RationalTy #Q

    StringTy
    SetTy

    SeqTy
    ArrayTy
    BitVecTy

  TypeId* = distinct int

const
  TypeKindBits = 8'u32
  TypeKindMask = (1'u32 shl TypeKindBits) - 1'u32

type
  TypeNode* = object     # 4 bytes
    x: uint32

template kind*(n: TypeNode): TypeKind = TypeKind(n.x and TypeKindMask)
template operand*(n: TypeNode): uint32 = (n.x shr TypeKindBits)
proc integralBits*(n: TypeNode): int {.inline.} =
  # Number of bits in the IntTy, etc. Only valid for integral types.
  assert n.kind in {IntTy, UIntTy, FloatTy, BoolTy}
  result = int(n.operand)

template toX(k: TypeKind; operand: uint32): uint32 =
  uint32(k) or (operand shl TypeKindBits)

import std / hashes
proc `==`*(a, b: TypeId): bool {.borrow.}
proc hash*(a: TypeId): Hash {.borrow.}

const
  Bool8Id* = TypeId 0
  Int8Id* = TypeId 1
  Int16Id* = TypeId 2
  Int32Id* = TypeId 3
  Int64Id* = TypeId 4
  UInt8Id* = TypeId 5
  UInt16Id* = TypeId 6
  UInt32Id* = TypeId 7
  UInt64Id* = TypeId 8
  Float32Id* = TypeId 9
  Float64Id* = TypeId 10
  
  BitVecId* = TypeId 11 # tmp, must be as non default node

type
  TypeGraph* = object
    nodes: seq[TypeNode]
    lit: Literals
  
  Literals* = ref object # it only need for when we get the sum types
    # strings*: BiTable[string]
    numbers*: BiTable[int64]

proc initTypeGraph*(lit: Literals): TypeGraph =
  result = TypeGraph(nodes: @[
    TypeNode(x: toX(BoolTy, 8'u32)),
    TypeNode(x: toX(IntTy, 8'u32)),
    TypeNode(x: toX(IntTy, 16'u32)),
    TypeNode(x: toX(IntTy, 32'u32)),
    TypeNode(x: toX(IntTy, 64'u32)),
    TypeNode(x: toX(UIntTy, 8'u32)),
    TypeNode(x: toX(UIntTy, 16'u32)),
    TypeNode(x: toX(UIntTy, 32'u32)),
    TypeNode(x: toX(UIntTy, 64'u32)),
    TypeNode(x: toX(FloatTy, 32'u32)),
    TypeNode(x: toX(FloatTy, 64'u32)),

    TypeNode(x: toX(BitVecTy, 0'u32)),
  ], lit: lit)

template `[]`*(t: TypeGraph; n: TypeId): TypeNode = t.nodes[n.int]
