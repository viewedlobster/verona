# Type system and motivation

* TODO: turn the code fragment below into actual code accepted by the compiler

## Questions

### Structural type system

* Why do we want a structural type system?

Left as an exercise for the reader.

TODO: ellen should write something here.

### Disjunction types: Why?

Gives us a way to take existing types/classes and easily describe groupings of
these. The main point is that this can be done after the fact of defining these
types/classes.

#### Implicit filtering on union types:
```ocaml
type t = A of t1
       | B of t2
       | C of t3


f (x : t) (g : ... -> s) =
    match x with
        A a => ...
        _   => g x
```
What is the type of g? With disjunction types we could represent t as
```verona
type T = T1 | T2 | T3

// g : T2 | T3 -> S
```
in ML we would have to construct an explicit type for this restriction and then
expand the match statement to deconstruct x and construct elements of this new
type.

#### Discrimination:
This type in ML
```ocaml
type t = A of int
       | B of int
```
Would perhaps be naively encoded like this 
```verona
type T = I32 | I32
```
but then we cannot discriminate between cases

But we can solve this by explicitly adding a level of types
```verona
class A { val: I32 } 
class B { val: I32 } 

type T = A | B
```

### Conjunction types: why?

#### Structural type system
Since our type system is structural, conjunction types is a convenient way to
express combinations of other types, like traits.
```verona

type A
type B
type C = A & B


interface C implements A, B {...}

f(x : A & B) = ...
```

Kind of the answer to multiple inheritance in C++.
```verona
// what would you write to inherit default implementations from Trait1 and
// Trait2?
class C : Trait1 & Trait2
// TODO need to check in compiler
```
#### Integration with capabilities

A type C with capability mut can be expressed as
```verona
C & mut
```

For generics, we don't need a quantifier specifically for capabilities. Instead
it's all part of the same type declaration.
```verona
type A[T] 

// can be instantiated to

A[mut & C]
```

Adding assumptions about types in a convenient way
```verona
type A[T] = {
    f(T & Imm) : S & Imm
}
// here we add the assumption that T is of Imm type in the method declaration
```

### Ad-hoc polymorphism:
#### Inheritance: Why don't we have it?
"Reuse is not subtyping", i.e. extending something does not imply subtyping.

```verona
class C {
    equal(self: C, other: C): Bool {...}
    f(...) : ... {...}
}

// here we want to reuse functionality of C in D, but we don't care about
// D <: C, i.e. using a D in the place for a C
class D : C {
    equal(self: D, other: D): Bool {...}
    g(...): ... { ... f(...) ... }
}
```
Note that this is imaginary syntax...

* TODO: check how you would actually write a thing like this in verona
* TODO: more concrete/realistic example

#### Traits

What we want from traits:
* A way to describe structural types
* Default implementations


A very basic example
```verona
type ToString = {
    toString(s: Self) : String
    print(s: Self) : Unit {
        sys.io.out(s.toString())
    }
}

let l : List[ToString]
```

* Question: Could we have a default implementation only in the case where Self <: ToString?
```verona
type ToString = {
    toString(s: Self) : String
}

type Printable = {
    print(s: Self) : Unit // this would have to be defined if Self </: ToString
} & {
    print(s: Self) : Unit where (Self <: ToString) {
        sys.io.out(s.toString())
    }
}

let l : List[ToString]
```


Question: do we want default implementations if not specified by the class
definition? E.g. type classes, or scala implicits.


Sidenote on haskell type classes.
```haskell
f :: Printable a => a -> IO ()

f x = ...
-- would be transformed into

f (dict :: Printable a) x = ...
```

#### Self types

* We have explicit self parameters to methods.
* Equality
``` verona
type Equalable = { equals(self : Self, other : Self) : Bool }
```


### Why `where`?

#### Method-level `where`
```verona
class Ref[T] {
    val : T
    get(self: Self) : T where T <: mut | imm // i.e. not iso
    {
        val
    }
    set(self: Self, v : T) : T { val = v }
}

class Array[T] {
    ...
    get(self: Self, idx : U32) : T where T <: mut | imm // i.e. not iso
    {
        ...
    }
    set(self: Self, idx : U32, v : T) : T { ... }
}

class Map[K, T] {
    ... // built on top of Array[T]
    get(self : Self, k : K) : T where T <: mut | imm // i.e. not iso
    {
        ...
    }
    set(self : Self, k : K, v : T) : T { ... }
}
```
In a system without method-level where clauses, we would need to bifurcate each
class on whether the class should be able to handle iso values or not.

#### Type level where

```verona
type Comparable = {
    compare(self : Self, other : Self) : Direction
}

type Direction = Above | Same | Below

// type Comparable[V] = {
//     compare(v1 : V, v2 : V) : Direction
// }

class RBTree[V] where (V <: Comparable) {...}
```

`where` clauses gives us a unified way of defining type constraints.

The alternative would be to have bounds for each parameter to a type:
```notverona
class RBTree[V <: Comparable] {...}
```

`where` clauses also allows us to give lower bounds.

Donno if useful
```verona
type Constraint[T] = List[T] <: ROList[T]
```
* TODO think about if there are any motivating examples

#### Subtype types (`T <: S`)
Lets us define constraints that can be reused
* TODO: is there anything in specific here

##### Related to subject/observer
Has stuff like this?
```verona
type Constraint[T] = T <: ROList[T]
```

* TODO: add subject/observer


### How does polymorphism look in our system?
### Fields vs methods


* Dynamic vs static dispatch
    - Universal call syntax
        + Syntax allows infixing
          ```verona
          f op g
          // If op is not in scope and f, g are expressions then this will be interpreted as
          f.op(g)
          ```
          Not really related to type system, but needs documenting somewhere.

