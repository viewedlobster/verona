# Subtyping rules


```cmath

t ::= t | t
    | t & t
    | ∀X. t
    | t[t]
    | c[t...]
    | τ{ f : t }
    | X
    | α
    | Self
    | t -> t
    | Top
    | Bot


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
type C = ∀X... . C[X...]

// C[X...] can be translated into the corresponding trait type with class_lookup
class_lookup(C, t...) = { /* clsbody */ }[t.../X...]

```


```cmath

σ(Γ) ⊢ σ'(Δ)
----
Γ ⊢ Δ
// σ, σ' are permutations of Γ, Δ


Γ, t1 & t2 ⊢ Δ
---- [conj-left]
Γ, t1, t2 ⊢ Δ


Γ ⊢ Δ, t1 & t2
---- [conj-right]
Γ ⊢ Δ, t1
Γ ⊢ Δ, t2


Γ, t1 | t2 ⊢ Δ
---- [disj-left]
Γ, t1 ⊢ Δ
Γ, t2 ⊢ Δ


Γ ⊢ Δ, t1 | t2
---- [disj-right]
Γ ⊢ Δ, t1, t2


Γ, X = A, B ⊢ Δ
---- [subst-left]
Γ, X = A, B[A/X] ⊢ Δ


Γ, X = A ⊢ Δ, B
---- [subst-right]
Γ, X = A ⊢ Δ, B[A/X]


Γ, A ⊢ Δ, A
---- [discharge-syntactic]


Γ, A <: B, A ⊢ Δ
---- [assume-sub]
Γ, A <: B, A, B ⊢ Δ


Γ, A -> B ⊢ Δ, A' -> B'
---- [arrow]
Γ*, A' ⊢ Δ*, A
Γ*, B  ⊢ Δ*, B'


// T[[\alpha]] is of the form   α [t] ... [t]
// where type application associate to the left
// thus we expand leftmost alias in a type application
Γ, T[[α]] ⊢ Δ
---- [alias-left]
alias_lookup(α) = A
Γ, T[[A]] ⊢ Δ


Γ ⊢ Δ, T[[α]]
---- [alias-right]
alias_lookup(α) = A
Γ ⊢ Δ, T[[A]]


Γ, c[t...] ⊢ Δ
---- [cls-left]
class_lookup(c, t...) = A
Γ, Self = c[t...], A ⊢ Δ


Γ, c[t...] ⊢ Δ, c[t'...]
---- [cls-right] // note the non-symmetry compared to alias rules
∀i ∈ [1, length(t...)]. Γ ⊢ Δ, tᵢ <: t'ᵢ


Γ, τ{ f : A } ⊢ Δ, τ'{ f : B }
---- [focus]
Γ, τ{ f : A } <: τ'{ f : B } ⊢ Δ, A <: B


Γ, (∀X. A) [B] ⊢ Δ
---- [appl-left]
Γ, A[B/X] ⊢ Δ


Γ ⊢ Δ, (∀X. A) [B]
---- [appl-right]
Γ ⊢ Δ, A[B/X]


// this should correspond to the typing rule in Kernel F_{<:}
Γ, ∀X. A ⊢ Δ, ∀Y. B
---- [poly]
Z fresh in (Γ, ∀X. A) and (Δ, ∀Y. B)
Γ, A[Z/X] ⊢ Δ, B[Z/Y]


Γ ⊢ Δ, A <: B
---- [sub-right]
Γ*, A ⊢ Δ*, B


Γ ⊢ Δ
---- [sub-assume]
Γ ⊢ A <: B
Γ, A <: B ⊢ Δ


---- [top]
Γ ⊢ Δ, Top


---- [bottom]
Γ, Bot ⊢ Δ


```