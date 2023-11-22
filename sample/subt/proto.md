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
=>
type C = ∀X... . C[X...]

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


Γ, A <: B, A, B ⊢ Δ
---- [assume-sub]
Γ, A <: B, A ⊢ Δ


Γ*, A' ⊢ Δ*, A
Γ*, B  ⊢ Δ*, B'
---- [arrow]
Γ, A -> B ⊢ Δ, A' -> B'


// T[[\alpha]] is of the form   α [t] ... [t]
// where type application associate to the left
// thus we expand leftmost alias in a type application
alias_lookup(α) = A
Γ, T[[A]] ⊢ Δ
---- [alias-left]
Γ, T[[α]] ⊢ Δ


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