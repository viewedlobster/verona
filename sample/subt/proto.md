# Questions

* How do we interpret method specialization with method-level where clauses from
  a formalization perspective?
* Implicit vs explicit recursive types
    - We use aliases for recursion, which is kind of implicit
    - Try to relate this to formal recursive types `μX. T`
* Where clauses:
    - How does this relate to conjunction types?

# Syntax of types

```cmath

t ::= t | t
    | t & t
    | c[t...]
    | α[t...]
    | τ{ f : mt }
    | X
    | Self
    | Top
    | Bot
    | t <: t

mt ::= [X...] mt_base where t

mt_base ::= t -> mt_base
          | t

τ ∈ TraitIdentifiers
α ∈ AliasNames

A, B are types in the rules below
```

# Denotation
```cmath
C ::= c[t...] (instantiated class)


t, i ⊧*ₙ t' iff ∀C. C, i ⊧ₙ t   =>   C, i ⊧ₙ t'


C, i ⊧ₙ t1 | t2 iff
    C, i ⊧ₙ t1   ∨   C, i ⊧ₙ t2


C, i ⊧ₙ t1 & t2 iff
    C, i ⊧ₙ t1   ∧   C, i ⊧ₙ t2


c[t...], i ⊧₀ c[t'...]


c[t...], i ⊧ₙ₊₁ c[t'...] iff
    ∀j.   t'ⱼ, i ⊧*ₙ tⱼ   ∧   tⱼ, i ⊧*ₙ t'ⱼ


C, i ⊧ₙ α[t...]   iff   C, i ⊧ₙ alias_lookup(α, t...)


// up to some renaming of params X...
C, i ⊧ₙ₊₁ τ{ f : [X...] t... -> t' where t'' } iff
    method_type(C, f) = [X...] s... -> s' where s''   ∧
    ∀Cs... . i' = i[X... ↦ Cs...]
             t'', i' ⊧*ₙ s''   ∧
             (Top, i' ⊧*ₙ t''   =>   ∀j.   tⱼ, i' ⊧*ₙ sⱼ   ∧
                                     s', i' ⊧*ₙ t')

// TODO there is currently two modes of binding: substitution (as in
//      method_type(c[t...], f)) and the variable mapping i. We should check if
//      this leads to problems and/or is unecessarily complicated.

C, i ⊧ₙ X   iff   C ∈ i[X]


// skipping Self for now


C, i ⊧ₙ Top   iff   true


C, i ⊧ₙ Bot   iff   false


C, i ⊧ₙ₊₁ t <: t'   iff   t, i ⊧*ₙ t'
```


# Subtyping rules


* TODO: add rule(s) for method signatures
```
[X...] mt where t <: [Y...] mt' where t'

Z... 

t'[Z.../Y...] <: t[Z.../X...]
```
We translate into types from code by the following transformation

```verona
class C[X...] {
    // clsbody
}
=>
type C = ∀X... . Cl[X...]

type A = ∀X... . { ... }


// TODO: write down rule where we do class lookup and polymorphism in one step
Γ, Self = Cl[t...], τCl{...} ⊢ Δ, { ... }[t'.../X...]
----
Γ, Cl[t...] ⊢ Δ, { ... }[t'.../X...]
----
Γ, ∀X... . Cl[X...] [t...] ⊢ Δ, ∀X... . { ... } [t'...]
----
Γ, C [t...] ⊢ Δ, A [t'...]


Γ, Self = Cl[t...], τCl{...} ⊢ Δ
----
Γ, C [t...] ⊢ Δ

// C[X...] can be translated into the corresponding trait type with class_lookup
class_lookup(C, t...) = { /* clsbody */ }[t.../X...]

```


```cmath

Γ ⊢ Δ
----
σ(Γ) ⊢ σ'(Δ)
// σ, σ' are permutations of Γ, Δ


Γ, t1, t2 ⊢ Δ
---- [conj-left]
Γ, t1 & t2 ⊢ Δ


Γ ⊢ Δ, t1
Γ ⊢ Δ, t2
---- [conj-right]
Γ ⊢ Δ, t1 & t2


Γ, t1 ⊢ Δ
Γ, t2 ⊢ Δ
---- [disj-left]
Γ, t1 | t2 ⊢ Δ


Γ ⊢ Δ, t1, t2
---- [disj-right]
Γ ⊢ Δ, t1 | t2


Γ, X = A, B[A/X] ⊢ Δ
---- [subst-left]
Γ, X = A, B ⊢ Δ


Γ, X = A ⊢ Δ, B[A/X]
---- [subst-right]
Γ, X = A ⊢ Δ, B


---- [discharge-syntactic]
Γ, A ⊢ Δ, A


Γ ⊢ Δ, A
Γ, B ⊢ Δ
---- [assume-sub] // (if Γ ⊢ A) should be a prerequisite in the implementation
Γ, A <: B ⊢ Δ


Γ*, A' ⊢ Δ*, A
Γ*, B  ⊢ Δ*, B'
---- [arrow]
Γ, A -> B ⊢ Δ, A' -> B'
// TODO: see the Self typing concern below

alias_lookup(α) = A[X...]
Γ, A[t.../X...] ⊢ Δ
---- [alias-left]
Γ, α[t...] ⊢ Δ

alias_lookup(α) = A[X...]
Γ ⊢ Δ, A[t.../X...]
---- [alias-right]
Γ ⊢ Δ, α[t...]

// T[[α]] is of the form   α [t] ... [t]
// where type application associate to the left
// thus we expand leftmost alias in a type application
// alias_lookup(α) = A
// Γ ⊢ Δ, T[[A]]
// ---- [alias-right]
// Γ ⊢ Δ, T[[α]]
// 
// alias_lookup(α) = A
// Γ, T[[A]] ⊢ Δ
// ---- [alias-left]
// Γ, T[[α]] ⊢ Δ

class_lookup(c) = A[X...]
Γ, Self = c[t...], A[t.../X...] ⊢ Δ
---- [cls-left]
Γ, c[t...] ⊢ Δ
// what is the ramifications of having one single Self


∀i ∈ [1, length(t...)]. Γ, c[t...] <: c[t'...] ⊢ (tᵢ <: t'ᵢ) & (t'ᵢ <: tᵢ)
---- [cls-right] // note the non-symmetry compared to alias rules
Γ, c[t...] ⊢ Δ, c[t'...]


// TODO A and B should be method types, make sure to expand and check
// co/contravariance
Γ*, τ{ f : A } <: τ'{ f : B }, A ⊢ B
---- [focus]
Γ, τ{ f : A } ⊢ Δ, τ'{ f : B }


// Γ, A[B/X] ⊢ Δ
// ---- [appl-left]
// Γ, (∀X. A) [B] ⊢ Δ
// 
// 
// Γ ⊢ Δ, A[B/X]
// ---- [appl-right]
// Γ ⊢ Δ, (∀X. A) [B]


// this should correspond to the typing rule in Kernel F_{<:}
Z fresh in (Γ, ∀X. A) and (Δ, ∀Y. B)
Γ, A[Z/X] ⊢ Δ, B[Z/Y]
---- [poly]
Γ, ∀X. A ⊢ Δ, ∀Y. B


Γ, A[X...] ⊢ Δ, B[Y...]




type A[X...]

type B[X...]

A[Z...] <: B[Z...]

Γ*, A ⊢ Δ*, B
---- [sub-right]
Γ ⊢ Δ, A <: B


Γ ⊢ A <: B
Γ, A <: B ⊢ Δ
---- [sub-assume]
Γ ⊢ Δ


---- [top]
Γ ⊢ Δ, Top


---- [bottom]
Γ, Bot ⊢ Δ


```


```verona
type Foo = { f : Self -> { g : Self -> Self } }
// what does the inner Self refer to
// every trait has its own Self binder?
```
* TODO: construct example where subtyping needs Self binders



cut is a use of a lemma 

```
Γ ⊢ A
Γ, A ⊢ Δ
---
Γ ⊢ Δ

```


# Self typing stuff

```verona

type A = {
    type Self
    type B = { g : Self -> A.Self }
    f : Self -> { g : Self -> A.Self }
}

type A' = {
    type Self
    type B' = { g : Self -> A'.Self }
    f : Self -> B'
}



```

```verona
// translation for Self types
type T = {
    f : Self -> S
}
=>
type T = {
    type Self // type declaration of Self
    f : T.Self -> S
}


type A = {
    f : Self -> { g : Self -> A.Self }
}
=>
type A = {
    type Self // type declaration of Self
    type Anon1 = { g : A.Anon.Self -> A.Self } // type definition of A.Anon1
    f : A.Self -> A.Anon1
}



type B[X] = {
    f : Self -> { g : Self -> X }
}
=>
type B[X] = {
    type Self
    type Anon1 = { g : B[X].Anon1.Self -> X }
    f : B[X].Self -> Anon1
}
// is B[X].Anon1.Self enough?

type B[X] = {
    f : Self -> { g : Self -> B[X].Self -> X }
}
=>
type B[X] = {
    type Self
    type Anon1[Y] = {
        g : B[X].Anon1[Y].Self -> Y
    }
    f : B[X].Self -> Anon1[X]
}
// is B[X].Anon1.Self enough?



type A = {
    type Anon = {
        h : A.Self -> Self
        i : Self -> A.Self
    }
    f : Self -> T
    g : S -> Self
    j : Self -> Anon
}
=>
type A[Self, AnonSelf] = {
    type Anon[Self, ASelf] = {
        h : ASelf -> Self
        i : Self -> ASelf
    }
    f : Self -> T
    g : S -> Self
    j : Self -> Anon[AnonSelf, Self]
}


class C {
    class D {
        h : C -> D
        i : D -> C
    }
    f : C -> T
    g : S -> C
    j : C -> D
}

C <: A[C, C::D]?


C <: A

```
```verona
// what does Self mean
type Comparable = {
    compare(s1 : Self, s2 : Self) : Direction
}

class RBTree[T] where (T <: Comparable) {
    ...
}

type X = RBTree[A | B]
```


```verona
type JSON = String | Number | Array[JSON]

type JSON' = String | Number | Array[JSON']

type Test = JSON <: JSON'

JSON <: JSON'
----
String | Number | Array[JSON] ⊢ String | Number | Array[JSON']
----
String ⊢ String, Number, Array[JSON'] // done
Number ⊢ String, Number, Array[JSON'] // done
Array[JSON] ⊢ String, Number, Array[JSON']


Array[JSON] ⊢ String, Number, Array[JSON']
----
JSON' <: JSON
JSON <: JSON'

```
