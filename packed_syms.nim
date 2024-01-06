# we store sym id as NIR sym id and count.
# since NIR's SymId used as node of NIR, then it have size <= 32 bits
# TODO: make sym storage

type
  PackedSymId* = distinct uint32#uint64

import std/hashes

proc `$`*(s: PackedSymId): string {.borrow.}
proc hash*(s: PackedSymId): Hash {.borrow.}
proc `==`*(a, b: PackedSymId): bool {.borrow.}

# NIR interaction

proc count*(s: PackedSymId): uint16 =
  s.uint16

import std/math
from Nim/compiler/nir/nirinsts import SymId
proc toPacked*(s: SymId; count: uint16): PackedSymId =
  assert s.uint32 <= static(2'u32^16)
  PackedSymId s.uint16 shl 16 or count

proc nirSymId*(s: PackedSymId): SymId =
  SymId s.uint64 shr 16
