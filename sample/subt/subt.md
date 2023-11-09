# General description
Our system only concerns itself with concrete classes, i.e. all type parameters
to classes must be instantiated.

What does this mean?

It means our domain for denotation should reflect this. I.e. that if we regard
types as sets, these are sets of concrete classes.

Can we fully instantiate a class, using only type parameters that are themself
classes? No, since we should be able to construct classes with complex type
parameters.

However, we can specify a denotation for type parameters as well, thereby
concretizing them.

How do we see the above relation as a fix point?

Is there a standard way to look at relations as fix points?


* what is o? and what properties does it have?
* examples of typechecking, construct classes and other stuff
  - list, map, cell
* what typing rules do we need?
* format of types: find as simple as possible format that can represent the
  types in the language


well-formedness used to generate tests for trieste.


* do we end up with a stronger typing judgement if we keep k qualifiers?

* types in where clause are restricted to subtype types.

* JLS 1.6?

constraint based subtyping with polymorphism is np hard and possibly undecidable

tiny bang


# Syntax
```cmath
t ::= t | t
    | t & t
    | { f[X...](t...) : t }
    | c[t...]           (non-recursive, for now)
//    | α                 (type alias)
//    | t where t
//    | Self
    | ∀x. t

//    | c[X...]  (why do we not care about these?)

A, B are t

c ::= (class names)

Γ, Δ ::= Γ, t
       | ε

// k ::= (fully qualified classes?)
```


# o is in A, denotation of types
```cmath
o ⊢ A



o ⊢ A | B   iff
    o ⊢ A    ∨    o ⊢ B

o ⊢ A & B   iff
    o ⊢ A    ∧    o ⊢ B

o ⊢ { f[X, Z](X) : X }
=>
o ⊢ { f[X, Z](Z) : X }

// how does subtyping of methods with type parameters work?
o ⊢ { f[X...](A...) : B where C }   iff
    mtype(o, f) = [X'...](A'...) : B' where C'                              ∧  // same number of parameters X... and X'..., A... and A'...
    forall T... .
        ((forall o'.   o' ⊢ C[T.../X...])   implies   (forall o'.   o' ⊢ C'[T.../X'...]))   ∧
        (forall i, o'.   o' ⊢ Ai[T.../X...]    implies    o' ⊢ A'i[T.../X'...])   ∧
        (forall o'.   o' ⊢ B'[T.../X'...]   implies   o' ⊢ B[T.../X...])

    // recursiveness?

// this definition could mean we can boil down a lot of things into
// conjunction with subtyping type
// type A[T] where (T <: B)  (== A[T] & (T <: B))  == ∀T. A[T] & (T <: B)
// o ⊢ (∀T. A[T] & (T <: B)) [B] ==> o ⊢ A[B] & (B <: B) ==> o ⊢ A[B]   ∧   o ⊢ (B <: B)
o ⊢ A <: B  iff
    forall o'. o' ⊢ A    implies    o' ⊢ B


o ⊢ Top   iff   True

// o ⊢ C[t...] iff
//     cname(o) == C    ∧    carg(o, i) <:> ti

o ⊢ C[A...] iff
    classname(o) == C    ∧    forall o', i.   o' ⊢ classarg(o, i)   <=>   o' ⊢ Ai

o ⊢ A[X...] where B   iff
    ∃T... . concrete(T)   ∧
            o ⊢ A[T.../X...]   ∧
            ∃o'.   o' ⊢ B[T.../X...]


// what is a concrete type?

// can we express everything using predicated types?
(X...) : U  where (X1 < T1) & (X2 < T2) & ...

// Would describe
(T...) : U

o ⊢ α[t...]   iff
    lookup(α) = t'[X...]    ∧
    o ⊢ t'[t.../X...]
```

```verona
type C[T] where T < B = {...}
```

```
OR(R) =  { o ⊢ A | B   s.t.   o ⊢ A ∈ R   ∨   o ⊢ B ∈ R }
AND(R) = { o ⊢ A & B   s.t.   o ⊢ A ∈ R   ∧   o ⊢ B ∈ R }
IFC(R) = { o ⊢ { f : A... -> B }   s.t.   mtype(o, f) = A'... -> B'   ∧
                                          ∀i, o'.   o' ⊢ Ai  ∈ R   =>   o' ⊢ A'i ∈ R   ∧
                                          ∀o'.      o' ⊢ B'i ∈ R   =>   o' ⊢ Bi  ∈ R     }
SUB(R) = { o ⊢ A <: B   s.t.   ∀o'.   o' ⊢ A ∈ R   =>   o' ⊢ B ∈ R }
 
```


```verona
type Storage[T] = {
    set : (Self, T) -> T
    get : (Self) -> T
}
// == { set: ... } & { get: ... }

class Cell[T] {
    set: (Cell[T], T) -> T
    get: (Cell[T]) -> T
}

type Test1[A] = Cell[A] <: Storage[A]

type A = Cell[X] | Cell[Y]
type B = Cell[Y] | Cell[X]

type Option[T] = Some[T] | None

type ImmList[T] where T < Imm = {
    append: (Self, T) -> Self
    head: (Self) -> Option[T]
    tail: (Self) -> Option[Self]
}

class LList[T] {
}
```


```
// is this needed?
---- [syntactic]
Γ, A ⊢ Δ, A


Γ, A ⊢ Δ
Γ, B ⊢ Δ
---- [disj-left]
Γ, A | B ⊢ Δ


Γ, A ⊢ Δ
---- [conj-left1]
Γ, A & B ⊢ Δ


Γ, B ⊢ Δ
---- [conj-left2]
Γ, A & B ⊢ Δ


Γ ⊢ A
Γ ⊢ B
---- [conj-right]
Γ ⊢ A & B


Γ ⊢ A
---- [disj-right1]
Γ ⊢ A | B


Γ ⊢ B
---- [disj-right2]
Γ ⊢ A | B

// can we make any assumptions here?
Γ ⊢  ti  <: ti'
Γ ⊢  ti' <: ti
---- [class]
Γ, c[t1, ...] ⊢ Δ, c[t1', ...]


Γ* , A ⊢ Δ*, B
----
Γ* ⊢ Δ*, A => B
----
Γ ⊢ Δ, box(A => B)





box(A => B)

sub_assumptions(Γ), A ⊢ B
----
Γ ⊢ Δ, A <: B

```

```cmath
// is this needed?
---- [syntactic]
Γ, A ⊢ Δ, A


Γ, A(k) ⊢ Δ
Γ, B(k) ⊢ Δ
---- [disj-left]
Γ, (A | B)(k) ⊢ Δ


Γ, A ⊢ Δ
---- [conj-left1]
Γ, (A & B)(k) ⊢ Δ


Γ, B ⊢ Δ
---- [conj-left2]
Γ, (A & B)(k) ⊢ Δ


Γ ⊢ A(k)
Γ ⊢ B(k)
---- [conj-right]
Γ ⊢ (A & B)(k)


Γ ⊢ A(k)
---- [disj-right1]
Γ ⊢ (A | B)(k)


Γ ⊢ B(k)
---- [disj-right2]
Γ ⊢ (A | B)(k)

// can we make any assumptions here?
Γ ⊢ Δ, ∀k. ti(k)  <: ti'(k)
Γ ⊢ Δ, ∀k. ti'(k) <: ti(k)
---- [class]
Γ, c[t1, ...](k) ⊢ Δ, c[t1', ...](k)


// ∀k. A <: B corresponds to us writing A < B
Γ, ∀k. A(k) <: B(k), A(k') <: B(k') ⊢ Δ
----
Γ, ∀k. A(k) <: B(k) ⊢ Δ


k' fresh
Γ ⊢ Δ, A(k') <: B(k')
----
Γ ⊢ Δ, ∀k. A(k) <: B(k)


Γ, A(k) ⊢ Δ, B(k)
----
Γ ⊢ Δ, A(k) <: B(k)
```


```verona
class C[X] {}
class D[Y] {}


type A
type B

type Test1 = C[A | B] <: C[B | A]
type Test2 = C[A & B] <: C[B & A]



---- [refl]
A(k') ⊢ ∀k. (A | B)(k) <: (B | A)(k), B(k'), A(k')
---- [disj-right]
(1.1)


A(k') ⊢ ∀k. (A | B)(k) <: (B | A)(k), (B | A)(k') (1.1)
B(k') ⊢ ∀k. (A | B)(k) <: (B | A)(k), (B | A)(k') (1.2)
---- [disj-left]
(A | B)(k') ⊢ ∀k. (A | B)(k) <: (B | A)(k), (B | A)(k')
---- [sub-right]
⊢ ∀k. (A | B)(k) <: (B | A)(k), (A | B)(k') <: (B | A)(k')
---- [forall-right]
(1)



⊢ ∀k. (A | B)(k) <: (B | A)(k) (1)
⊢ ∀k. (B | A)(k) <: (A | B)(k) (2)
---- [class]
C[A | B](k') ⊢ ∀k. C[A | B](k) <: C[B | A](k), C[B | A](k')?
---- [sub-right]
⊢ ∀k. C[A | B](k) <: C[B | A](k), C[A | B](k') <: C[B | A](k')?
---- [forall-right]
⊢ ∀k. C[A | B](k) <: C[B | A](k)?
```

k are classes with no free variables, i.e. all parameters instansiated.
```

Γ ⊢ A[c]
Γ, B[c] ⊢ Δ
c not in Γ
----
Γ, ∀c. A <: B ⊢ Δ


----
Γ, A[c] <: B[c], A[c] ⊢ B[c]



c' fresh
Γ, ∀c. A <: B, (A <: B)[c/c'] ⊢ Δ
----
Γ, ∀c. A <: B ⊢ Δ
```

```cmath
[[ A | B ]] = [[ A ]] ∪ [[ B ]]

[[ A & B ]] = [[ A ]] ∩ [[ B ]]

// this definition is sound since there is no recursion
[[ c[t1,...] ]] = { c[ [[ t1 ]], ... ] }
```

How do we model concrete classes?


```verona
class C[T] {}
class TypeEq[A, B] where A < B & B < A {}

type A
type B
type X = C[A | B]
type Y = C[B | A]

let test1 : TypeEq[A, A]
let test2 : TypeEq[C[A | B], C[B | A]]
```

# Questions to answer

- what should we model types with?
- what is the denotation of types?
- what subtyping rules do we need?
- how to handle polymorphism?
- how to handle where clauses?
- how to handle recursion?
