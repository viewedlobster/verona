# Questions

* How do we interpret method specialization with method-level where clauses from
  a formalization perspective?
* Implicit vs explicit recursive types
    - We use aliases for recursion, which is kind of implicit
    - Try to relate this to formal recursive types `μX. T`
* Where clauses:
    - How does this relate to conjunction types?

# Subtyping rules


```cmath

t ::= t | t
    | t & t
    | ∀X. t
    | t [t]
    | c[t...]
    | τ{ f : t }
    | X
    | α
    | Self
    | t -> t
    | Top
    | Bot
    | t <: t


τ ::= τid[t...]


τid ∈ TraitIdentifiers

α ∈ AliasNames

A, B are types in the rules below


// we want to be able to expand leftmost alias in a type application
T ::= [[⋅]]
    | T [t]
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
---- [assume-sub] (if Γ ⊢ A)
Γ, A <: B ⊢ Δ


Γ*, A' ⊢ Δ*, A
Γ*, B  ⊢ Δ*, B'
---- [arrow]
Γ, A -> B ⊢ Δ, A' -> B'
// TODO: see the Self typing concern below

// T[[\alpha]] is of the form   α [t] ... [t]
// where type application associate to the left
// thus we expand leftmost alias in a type application
alias_lookup(α) = A
Γ, T[[A]] ⊢ Δ
---- [alias-left]
Γ, T[[α]] ⊢ Δ

// type Alias1 = ∀X. {...}
// Alias1 [t...] => ∀X. {...}

alias_lookup(α) = A
Γ ⊢ Δ, T[[A]]
---- [alias-right]
Γ ⊢ Δ, T[[α]]


class_lookup(c, t...) = A
Γ, Self = c[t...], A ⊢ Δ
---- [cls-left]
Γ, c[t...] ⊢ Δ


∀i ∈ [1, length(t...)]. Γ ⊢ Δ, tᵢ <: t'ᵢ
---- [cls-right] // note the non-symmetry compared to alias rules
Γ, c[t...] ⊢ Δ, c[t'...]


Γ, τ{ f : A } <: τ'{ f : B } ⊢ Δ, A <: B
---- [focus]
Γ, τ{ f : A } ⊢ Δ, τ'{ f : B }


Γ, A[B/X] ⊢ Δ
---- [appl-left]
Γ, (∀X. A) [B] ⊢ Δ


Γ ⊢ Δ, A[B/X]
---- [appl-right]
Γ ⊢ Δ, (∀X. A) [B]


// this should correspond to the typing rule in Kernel F_{<:}
Z fresh in (Γ, ∀X. A) and (Δ, ∀Y. B)
Γ, A[Z/X] ⊢ Δ, B[Z/Y]
---- [poly]
Γ, ∀X. A ⊢ Δ, ∀Y. B


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