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
This IR uses SSA, so variable can have only one assigment. It allows to add checks that creates new facts without future collision in SMT solver, for example
```nim
var a = 5
assert a <= 7
a += 3
```
IR:
```nim
a = Scalar {Int 5}
Checked {0 Assert a <= 7}
a_2 = Add {a 5}
```
If a_2 is a:
```nim
a = 5
assert a <= 7 # proven => fact a <= 7
a += 3
```
when seeing that isSat we have that
a = 8
and fact: a <= 7
=> unsat
therefore it is necessary to use SSA.

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

Facts
=====
If the check is proved or cannot be proved, it becomes a fact.
When check can't be proved, in any case, it will be added in real time and if there is no error, then it is correct, i.e. this is a fact and we can further build static analysis on this, else there will be just a real-time error and that’s it.

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
Checked {
  0 # is fact or not
  Range
  Constraint x >= 1
  Constraint x <= 6
}
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
```

Sum types
=========
In section below we can see how represented objects (product types) but we also need a sum types.
nim:
```nim
type Test = enum
  A
  B

var x = A
```
IR:
```
a = Scalar {<Test> 0}
```
And Test type defined in type system as SumType

Control flow
============
P.S. Next to implement

It very similar to DrNim Phi nodes, as in DrNim, 
here expressions are used instead of blocks.
(There's no point in complicating this if by default the node just exists anyway.)


Nim:
```nim
var x = y
if a:
  inc x
elif b:
  inc x, 2
```
IR:
```nim
x_0 = y

x_1 = x_0 + 1
x_2 = x_0 + 2

Checked {
  # checks is need in all branches, not only on Phi node
  # controversial decision, but even on a branch that will never execute, 
  # allowing bad code is not a good idea
  0
  Overflow
  x_1 <= 2^32
}

Checked {
  0
  Overflow
  x_2 <= 2^32
}

Phi {
  SymUse x_3

  Det { # Det node can show the branch that need to select
    a # det, if true ---> select branch. if one true then other --> false. 
      # this value must be pinpoint the branch
    x_1
  }
  Det {
    b and not a
    x_2
  }
  Det {
    not(a or (b and not a)) # Note other must be not of other det
    x_0
  }
}
```
For loops it uses an Loop Closed SSA (LCSSA).
It means that all values that are defined in a loop are used only inside this loop.
Nim:
```nim
var y = 4
for i in 0..<5:
  y = 7
```
IR:
```nim
y_0 = 4

# Loop body start
y_1 = 7 # it can be, or it can not be, we a don't know and it doesn't matter to us

# Loop body end

# Invariant i:
i = Scalar {
  Int
  None # we don't know i val
}

i_min = 0
i_max = 4

Checked {
  0
  Range
  i >= i_min
  i <= i_max
}

y_2 = Phi {
  SymUse i # param

  Det {
    i < i_min
    y_0
  }
  Det {
    i >= i_min
    y_1
  }
}
```

Phi logic can better explained here
Nim:
```nim
var y = 4
for i in 0..<5:
  y *= 2
```
IR:
```nim
y_0 = 4

i = Scalar {
  Int
  None
}

i_min = 0
i_max = 4

Checked {
  0
  Range
  i >= i_min
  i <= i_max
}

# on fact it's recursive function that describe the Phi hierarhy
# it's alternative to basic blocks
# Phi in LLVM means that if you are from selected block then selected branch
# Phi in SMTIR means that if predicate true then selected branch.
# Because of this to allow not linear graphs we make Phi parametric

y_1 = Phi {
  SymUse i

  Det {
    i < i_min
    y_0
  }
  Det {
    i != 0
    ResolvedPhi {
      SymUse y_1
      i - 1
    } * 2
  }
} # it is unknown what 
  # the consequences of using this instead of basic blocks will be
  # Fun fact: if we think of this as a recursive function, 
  # the SMT solver will be able to find an i 
  # that will give the desired value for y
  # this representation also very simple can determine the arith (and geom) 
  # progression and replace it by formulas

y_2 = ResolvedPhi {
  y
  i_max # parameters to resolve
}
```

Simplifier
==========
NOTE: Very hard to implement but necessary

Progressions in loop
Nim:
```
var y = 6
for i in 0..1:
  y *= 2 # y = y * 2
```
Ir:
```nim
y_1 = Phi {
  SymUse i

  Det {
    i < i_min
    y_0
  }
  Det {
    i >= i_min
    ResolvedPhi {
      SymUse y_1
      i - 1
    } * 2
  }
}
```
Pseudo: phi(i) = phi(i - 1) * 2
It means that it is nth term of geom progression.
so
```
y_1 = Phi {
  SymUse i

  Det {
    i < i_min
    y_0
  }
  Det {
    i >= i_min
    y_0 * 2^(i - i_min + 1 - 1)
  }
}
y_2 = ResolvedPhi {
  SymUse y_1
  i_max
}
```

Nim:
```
var y = 6
for i in 0..1:
  y += y * 2 # y = y + y * 2
```
Ir:
```nim
y_1 = Phi {
  SymUse i

  Det {
    i < i_min
    y_0
  }
  Det {
    i != 0
    Add {
      ResolvedPhi {
        SymUse y_1
        i - 1
      }
      Mul {
        ResolvedPhi {
          SymUse y_1
          i - 1
        }
        Scalar {Int 2}
      }
    }
  }
}
```
Pseudo: phi(i) = phi(i - 1) + phi(i - 1) * 2
Expr phi(i) = phi(i - 1) + sth ---> sth is sum i_max - i_min times.
sth = phi(i - 1) * 2 same as old example it's means that it is nth term of geom progression
Expr phi(i) = phi(i - 1) + nth_term(geom) => sum of geom progression


Future directions / The long run
================================

Intrinsics
==========
It's possible to use SMT solver for intrinsics

example of this: https://github.com/zwegner/x86-sat

Concurrent code analysis
========================
https://dl.acm.org/doi/10.1145/3335149

Recursive functions analysis
============================
Requirements:
1. Function is deterministic
2. (Maybe) Function should be bijection

Prove that recursion terminated
http://lara.epfl.ch/~kuncak/papers/SuterETAL11SatisfiabilityModuloRecursivePrograms.pdf
https://www.cs.cornell.edu/courses/JavaAndDS/files/recursionbf.pdf
https://www.fstar-lang.org/tutorial/book/part1/part1_termination.html

Let us have a measure that depends on the arguments of the function and returns number. Each new (different) call creates a new measure. If new measure > old, function is non terminated.

let p is any base case, for fib it's x = 0, x in {1, 2}
measure(p) <= 0
for recursive case measure > 0

```nim
proc fib(n: int): int =
  if n == 0: 0
  elif n < 3: 1
  else: fib(n - 1) + fib(n - 2)
```
known facts:
measure(n == 0) <= 0
measure(n < 3) <= 0
measure(not(n == 0 or n < 3)) > 0

inner measure must be smaller, it means that we need to prove that
measure(n - 1) < measure(n)
measure(n - 2) < measure(n)

And it can be simply proved by induction
measure(n - 1) < measure(n)
measure(n - 2) < measure(n - 1) < measure(n)
...
measure(n < 3) < measure(n)

measure(n < 3) <= 0
measure(n) > 0, so it proved

```nim
proc inf(n: int): int = inf(n - 1)
```
facts:
measure(n) > 0
measure(n - 1) > 0

measure(n - 1) < measure(n)

we can't prove that measure(n - 1) < measure(n), it is not terminated

```nim
proc inf(n: int): int = inf(n)
```
facts:
measure(n) > 0
measure(n) < measure(n) => 0 < 0 => W

Limitation:
Note: this fib is also untermiated, but proved:
```nim
proc fib(n: int): int =
  if n == 0: 0
  elif n in [1, 2]: 1
  else: fib(n - 1) + fib(n - 2)
```
we can get fib(-1) and it will endless (until StackOverflowError).
for make it termianted we need say that n >= 0.
facts:
fib(0) = 0
fib(1) = fib(2) = 1
fib(n != {0, 1, 2}) = fib(n - 1) + fib(n - 2)

to prove:
m: m != {0, 1, 2}
fib(m - 1) < fib(m)
fib(m - 2) < fib(m)

fib(m - 2) < fib(m - 1) =>
fib(2) < fib(3) => proved, but it wrong, because we can use n < 0, this step is because m > 3, we can't do this step is m < 0.

In theory this should also work with non-primitive recursive functions
```nim
proc ackermann(n, m: int): int =
  if n == 0: m + 1
  elif m == 0: ackermann(n - 1, 1)
  else: ackermann(n - 1, ackermann(n, m - 1))
```
facts:
measure(0, m) <= 0
measure(n, 0) > 0
measure(n != 0, m != 0) > 0

to prove:
measure(n - 1, 1) < measure(n, 0) # n = 1
measure(n - 1, measure(n, m - 1)) < measure(n != 0, m != 0)
=>
we need to prove that
measure(0, 1) < measure(1, 0)

measure(0, 1) <= 0
measure(1, 0) > 0
it means that function terminated

General algorithm: if we have x1, x2, x3, ..., xn that can be used in measure than the func terminated. It not perfect, because it says that func terminated if it has at least one args combination in which this is not terminated, but through quantifiers it does not work normally.

Also recursive functions analysis can be useful for recursive functions optimization. Note: it's very hard.
Must be better than tail call optimization.

```nim
proc fib(n: int): int =
  if n == 0: 0
  elif n < 3: 1
  else: fib(n - 1) + fib(n - 2)
```
Uses recursive functions theory

let `fib` is recursive function with body:
```py
If(
  n == 0, 
  0, 
  If(
    n < 3, 
    Int(1), 
    fib(n - 1) + fib(n - 2)
  )
)
```
For optimizing we need produce code like this

(with refinement types no if, but that's not that important)

It in general, for alghorithm like this, of course
 Matrix exponentiation and Fast doubling is faster.

```nim
proc fib(n: int): int =
  if n == 0: return 0
  result = 1
  var old = 1
  for i in 2..<n:
    (result, old) = (result + old, result)
```

This may seem complicated, but it's not entirely true.
First, we know that for any recursion need to modify different call comb vals.
```nim
proc f(x: int): int =
  ...
  let a = f(x - 1) + f(x - 5) + f(x - 8)
  let b = f(x - 1)
```
As we know that f deterministic, a = b + f(x - 5) + f(x - 8) and
we need to store 3 vals: x - 1, x - 5, x - 8

It might seem like we should just use quantifiers, but it have one problem. Quantifiers are hard for SMT solvers. Recursive definitions are hard for SMT solvers. It means that we should not use it both (It don't include inner func analysis with quantifiers).
