For static code analysis purposes we use the SMT immediate representation.
It can generate code for SMT solvers.
All main steps:
```
NIR ---> SmtIR --> Simplifier +-> SmtIR  +--> Z3   -----+
         ^                    |          |--> CVC5 ---+ |
         |                    |                       | |
Ast -----+                    +---------------------> SMT verdict
```
SmtIR can handle refirement types via `StopPoint`

General
=======
This IR uses SSA, so variable can have only one assigment

IR type system contains only primitive types without user defined. See objects section.

It designed for simple mapping to SMT solvers, so some things like SMT constr.

Types
=====
IR types is very different from nim types. Some types from the standard library are primitive types. For example, rationals, it's primitive type in IR.

Interaction with external code
==============================
`StopPoint` node can show when the refinement type
```nim
some code
StopPoint # we a run onStopPoint callback
some other code
```
`Coupled` node makes symbols coupled, it means that if one symbol need in program, other also need.
```nim
Coupled {
  SymUse a
  SymUse b
  SymUse c
}
```
in example if we need to use in program a sym, code with b and c syms also
stays after `simplifier`
`Refinement` node can show that value is refinement

Arrays
======
Arrays represented as Vector (just fixed-length seq of values)

Nim:
```nim
var a = [1, 2]
a[0] = 3
```
IR:
```nim
a = Vector {
    Int64
    Scalar {Int64 1}
    Scalar {Int64 2}
}
VectorAt {SymUse a 0} = Scalar {Int64 3}
```
Nim arrays can starts from any num:
```nim
var a: array[1..2, int] = [1, 2]
```
IR:
```nim
a = Vector {
    Int64
    Offset 1
    Scalar {Int64 1}
    Scalar {Int64 2}
}
```


N-dim arrays represented as flatten. For array starting points also need offsets
```nim
var a = [
  [1, 2],
  [3, 4]
]

a[1][1] = 5
```
IR:
```nim
a = Vector {
    Int64
    Scalar {Int64 1}
    Scalar {Int64 2}
    Scalar {Int64 3}
    Scalar {Int64 4}
}
VectorAt {SymUse a 3} = Scalar {Int64 5} # 1*2 + 1*1
```

Ranges
======
Nim:
```nim
var x: range[1..6] = 3
```
IR:
```nim
x = Scalar {Int64 3}
Constraint x >= 1
Constraint x <= 6
``` 

Objects
=======
SMTir handles objects to just different values

i.e.
Nim:
```nim
type A = object
  x: int32
  y: int32

var a = A(x: 5, y: 8)
```
IR:
```nim
a.x = Scalar {Int 5}
a.y = Scalar {Int 8}

Coupled {
  ExternalSymUse a
  SymUse a.x
  SymUse a.y
}
```

Of course it supports casting between objects and types

Nim:
```nim
type A = object
  x: int32
  y: int32

var a = A(x: 5, y: 8)
var b = cast[int64](a)
```
IR:
```nim
a.x = Scalar {Int32 5}
a.y = Scalar {Int32 8}

Coupled {
  ExternalSymUse a
  SymUse a.x
  SymUse a.y
}

a.x_bitvec = Conv {
  Int32
  BitVec
  SymUse a.x
}

a.y_bitvec = Conv {
  Int32
  BitVec
  SymUse a.y
}

b = Concat {
  SymUse a.x_bitvec
  SymUse a.y_bitvec
}
```

And object to object casting
Nim:
```nim
type A = object
  x: int32
  y: int32

type B = object
  x: int16
  y: int16
  z: int32

var a = A(x: 5, y: 8)
var b = cast[B](a)
```
IR:
```nim
a.x = Scalar {Int32 5}
a.y = Scalar {Int32 8}

Coupled {
  ExternalSymUse a
  SymUse a.x
  SymUse a.y
}

a.x_bitvec = Conv {
  Int32
  BitVec
  SymUse a.x
}

a.y_bitvec = Conv {
  Int32
  BitVec
  SymUse a.y
}

c = Concat {
  SymUse a.x_bitvec
  SymUse a.y_bitvec
}

b.x = Extract {
  Range {
    min: 0
    max: 16
  }
  SymUse c
}

b.y = Extract {
  Range {
    min: 16
    max: 32
  }
  SymUse c
}

b.z = Extract {
  Range {
    min: 32
    max: 64
  }
  SymUse c
}

Coupled {
  ExternalSymUse b
  SymUse b.x
  SymUse b.y
  SymUse b.z
}