# System F-like stuff


```cmath

t ::= t | t
    | t & t
    | ∀X. t
    | c[t...]
    | { f : mtype }
    | Self
    | α
    | Top
    | Bot

mtype ::= ∀X. mtype
        | t & mtype_base

mtype_base ::= (t...) -> t
```


# Even more System F-like

```cmath

t ::= t | t
    | t & t
    | ∀X. t
    | c[t...]
    | { f : t }
    | Self
    | α
    | t -> t
    | Top
    | Bot
```


```cmath
o, slf ⊢ t1 | t2 iff
    o ⊢ t1   ∨   o ⊢ t2


o, slf ⊢ t1 & t2 iff
    o ⊢ t1   ∧   o ⊢ t2


o, slf ⊢ ∀X. t iff
    forall t' o'. o' ⊢ o [t']   implies   o' ⊢ t[t'/X]


o, slf ⊢ C[t...] iff
    class_name(o) == C   ∧
    forall i o'.   o' ⊢ class_arg(o, i)   iff   o' ⊢ ti
// class_arg(o, i) = ith argument to o class

o, slf ⊢ { f : t } iff
    mtype(o, f) = t'   ∧
    forall o'.   o', o ⊢ t'   implies   o', o ⊢ t  // set slf = o
    // Self type?


o, slf ⊢ Self iff slf =sub= o
```


```verona

type I = {
    var f : T
} & {
    clone : I -> I
}

type J = {
    clone : J -> J
}

class C {
    clone : C -> C
}

J <: C 
C <: J
----
C <: J

type Deep = {
    deep : Self -> Self
}

type Shallow = {
    shallow : Self -> Self
}

type Both = Deep & Shallow

A <: B

Γ, Δ ::= t, Γ
       | ε

∧(Γ) ⊢ ∨(Δ)
// Can we interpret Self as an implicit recursive type?
// Both <: Shallow? Pretty easy to prove just using syntactic equality of Self
// from top to bottom:
{ shallow : Self -> Self } & { deep : Self -> Self } ⊢  { shallow : Self -> Self }
---- [conj-left]({ shallow : Self -> Self } & { deep : Self -> Self })
{ shallow : Self -> Self }, { deep : Self -> Self } ⊢ { shallow : Self -> Self }
---- [syntactic-eq]({ shallow : Self -> Self })
// analogous for Both <: Deep...

class C {
    deep : C -> C
}

⊢ C <: Deep
---- [modallogicthing]
⊢ C => Deep
---- [impl-right]
C ⊢ Deep


// if we wanna subtype a class we need to replace Self with C
C ⊢ Deep
---- [alias-right](Deep)
C ⊢ { deep : Self -> Self }
---- [cls-left](C, Self = C)
Self = C, { deep : C -> C } ⊢ { deep : Self -> Self }
---- [subst-right](Self = C, { deep : Self -> Self })
Self = C, { deep : C -> C } ⊢ { deep : C -> C }
---- [syntactic-eq]({ deep : C -> C })

// Self = C[Self] - this is bad, probably need well formedness

class D {
    deep : D -> D,
    forget : D -> D
}

type Forget = {
    forget : Forget -> Forget
}

// if we have Forget, a recursive trait type
D ⊢ Forget
---- [alias-right](Forget)
D ⊢ { forget : Forget -> Forget }
---- [cls-left](D, Self = D)
Self = D, { deep : D -> D, forget : D -> D } ⊢ { forget : Forget -> Forget }
----
Self = D, { deep : D -> D }, { forget : D -> D } ⊢ { forget : Forget -> Forget }
// to make this subtyping relation hold we need D <: Forget & Forget <: D
// which isn't possible, even with recursive assumptions
// D <: Forget comes from recursive assumption, but not Forget <: D


// If we change definition of forget to
type Forget' = {
    forget : Self -> Forget'
}

class D' {
    forget : D' -> D'
}

D' ⊢ Forget'
---- [alias-right](Forget')
D' ⊢ { forget : Self -> Forget' }
---- [cls-left](D', Self = D')
Self = D', { forget : D' -> D' } ⊢ { forget : Self -> Forget' }
---- [subst-right](Self = D', { forget : Self -> Forget' })
Self = D', { forget : D' -> D' } ⊢ { forget : D' -> Forget' }
---- [record-focus](forget)
Self = D', D' <: Forget, D' -> D' ⊢ D' -> Forget'
---- [function]
(1) Self = D', D' ⊢ D' // follows immediately
(2) Self = D', D' ⊢ Forget' // need recursive subtyping assumption here

// cyclic proof: anything higher up the tree can be used as assumption as long
// as path back is through a record-focus rule. Look up cyclic proof theory.
// James Brotherstone

// other solution would be to have named traits in types, which is closer to
// what the implementation uses.
// for now, tag a trait with the type alias under which it is defined
D' ⊢ Forget'
---- [alias-right](Forget')
D' ⊢ Forget'{ forget : Self -> Forget' }
---- [cls-left](D', Self = D')
Self = D', D'{ forget : D' -> D' } ⊢ Forget'{ forget : Self -> Forget' }
---- [subst-right](Self = D', { forget : Self -> Forget' })
Self = D', D'{ forget : D' -> D' } ⊢ Forget'{ forget : D' -> Forget' }
---- [member-focus](forget) // since we focus member in D'/Forget' we add assumption that D' <: Forget'
Self = D', D' <: Forget', D' -> D' ⊢ D' -> Forget'
---- [function]
(1) Self = D', D' <: Forget', D' ⊢ D' // follows immediately
(2) Self = D', D' <: Forget', D' ⊢ Forget' // need recursive subtyping assumption here

// solution(?) 1:
type Alias1 = { f : A -> Alias1 } & { g : B -> Alias1 }
// equiv to
// type Alias1 = Alias1{ f : A -> Alias1 } & Alias1{ g : B -> Alias1 }


// solution(?) 2:
type Alias2 = { f : A -> Alias2 } & { g : B -> Alias2 }
// equiv to
type Alias2 = Alias2_1{ f : A -> Alias2 } & Alias2_2{ g : B -> Alias2 }


class E {
    f : A -> E
    g : B -> E
}

// TODO an example where we have replace Self = C with Self = D, i.e. a case
// where we have some recursive case where we need to verify D <: T1 in order to
// verify C <: T2

//type Alias1 = A1' & A1''
//
//
//alias_expand(Alias1, A1' & A1'') = 
//Alias1#A1' & Alias1#A2'
//A1'#{...} & A2'#{...}
//Alias1#{...} & Alias1#{...}

// Subtyping with solution 1:
E ⊢ Alias1
---- [alias-right](Alias1)
E ⊢ Alias1{ f : A -> Alias1 } & Alias1{ g : B -> Alias1 }
---- [cls-left](E, Self = E)
Self = E, E{ f : A -> E } & E{ g : B -> E } ⊢ Alias1{ f : A -> Alias1 } & Alias1{ g : B -> Alias1 }
---- [conj-left](E{ f : A -> E } & E{ g : B -> E })
Self = E, E{ f : A -> E }, E{ g : B -> E } ⊢ Alias1{ f : A -> Alias1 } & Alias1{ g : B -> Alias1 }
---- [conj-right]
(1) Self = E, E{ f : A -> E }, E{ g : B -> E } ⊢ Alias1{ f : A -> Alias1 }
(2) Self = E, E{ f : A -> E }, E{ g : B -> E } ⊢ Alias1{ g : B -> Alias1 } // similar to (1)


(1)
---- [record-focus](f, E <: Alias1)
E <: Alias1, Self = E, A -> E ⊢ A -> Alias1
---- [function]
(1.1) E <: Alias1, Self = E ⊢ A <: A
(1.2) E <: Alias1, Self = E ⊢ E <: Alias1


(1.1)
---- [modal](A <: A)
E <: Alias1, Self = E ⊢ A => A
---- [impl-left](A => A)
E <: Alias1, Self = E, A ⊢ A
---- [syntactic](A)

(1.2)
---- [syntactic](E <: Alias1)


// subtyping with solution 2:
E ⊢ Alias1
---- [alias-right](Alias1)
E ⊢ Alias1_1{ f : A -> Alias1 } & Alias1_2{ f : B -> Alias1 }
---- [cls-left](E)
Self = E, E_1{ f : A -> E } & E_2{ g : B -> E } ⊢ Alias1_1{ f : A -> Alias1 } & Alias1_2{ g : B -> Alias1 }
---- [conj-left]
Self = E, E_1{ f : A -> E }, E_2{ g : B -> E } ⊢ Alias1_1{ f : A -> Alias1 } & Alias1_2{ g : B -> Alias1 }
---- [conj-right]
(1) Self = E, E_1{ f : A -> E }, E_2{ g : B -> E } ⊢ Alias1_1{ f : A -> Alias1 }
(2) Self = E, E_1{ f : A -> E }, E_2{ g : B -> E } ⊢ Alias1_2{ g : B -> Alias1 }

(1)
---- [record-focus](E_1, Alias1_1, f)
E_1 <: Alias1_1, Self = E, A -> E ⊢ A -> Alias1
---- [method]
(1.1) E_1 <: Alias1_1, Self = E ⊢ A <: A // trivial
(1.2) E_1 <: Alias1_1, Self = E ⊢ E <: Alias1

(1.2)
----...
E_1 <: Alias1_1, Self = E, E ⊢ Alias1
---- [alias-right]
E_1 <: Alias1_1, Self = E, E ⊢ Alias1_1{ f : A -> Alias1 } & Alias1_2{ g : B -> Alias1 }
---- [cls-left]
E_1 <: Alias1_1, Self = E, Self = E, E_1{ f : A -> E } & E_2{ g : B -> E } ⊢ Alias1_1{ f : A -> Alias1 } & Alias1_2{ g : B -> Alias1 }
---- [conj-left]
E_1 <: Alias1_1, Self = E, Self = E, E_1{ f : A -> E }, E_2{ g : B -> E } ⊢ Alias1_1{ f : A -> Alias1 } & Alias1_2{ g : B -> Alias1 }
---- [conj-right]
(1.2.1) E_1 <: Alias1_1, Self = E, Self = E, E_1{ f : A -> E }, E_2{ g : B -> E } ⊢ Alias1_1{ f : A -> Alias1 }
(1.2.2) E_1 <: Alias1_1, Self = E, Self = E, E_1{ f : A -> E }, E_2{ g : B -> E } ⊢ Alias1_2{ g : B -> Alias1 }


(1.2.1)
---- [discharge-sub](E_1{...}, E_1 <: Alias1_1, Alias_1{...}) // nrule to discharge Alias1_1{ f : A -> Alias1 } using E_1 <: Alias1_1 and E_1{ f : A -> E }

(1.2.2) 
---- [record-focus](E_2, Alias1_2, g)
E_1 <: Alias1_1, E_2 <: Alias1_2, Self = E, Self = E, B -> E ⊢ B -> Alias1
---- [method]
...
----
(1.2.2.1) E_1 <: Alias1_1, E_2 <: Alias1_2, Self = E, Self = E, B ⊢ B // trivial
(1.2.2.2) E_1 <: Alias1_1, E_2 <: Alias1_2, Self = E, Self = E, E ⊢ Alias1

(1.2.2.2)
---- [alias-right](Alias1) then [cls-left](E)
E_1 <: Alias1_1, E_2 <: Alias1_2, Self = E, Self = E, Self = E, E_1{ f : A -> E } & E_2{ g : B -> E } ⊢ Alias1_1{ f : A -> Alias1 } & Alias1_2{ g : B -> Alias1 }
---- [conj-left] then [conj-right]
(1.2.2.2.1) E_1 <: Alias1_1, E_2 <: Alias1_2, Self = E, Self = E, Self = E, E_1{ f : A -> E }, E_2{ g : B -> E } ⊢ Alias1_1{ f : A -> Alias1 } // by discharge-sub
(1.2.2.2.2) E_1 <: Alias1_1, E_2 <: Alias1_2, Self = E, Self = E, Self = E, E_1{ f : A -> E }, E_2{ g : B -> E } ⊢ Alias1_2{ g : B -> Alias1 } // by discharge-sub
// this is fucking long...



// TODO can we construct System F similie but with self types?

type A = {
    // in the case where X </: B, the type (X <: B) is equiv to Bot, and
    // therefore the term (λx. x) does not satisfy the type (X <: B) & (X -> X)
    // can we include some construct to condition term on subtyping
    // - monomorphising?
    f : ∀X. (X <: B) & (X -> B) = ΛX. If (X <: B) Then λx. x Else error
    g : ∀X. (X <: B) & (X -> B) = ΛX. (λx. x) where (X <: B)
}

// from a subtyping point of view: is where and & equivalent?
// from a term typing point of view: do we need additional constructs like the
// above to type terms under such types?


// this is unsound
D' ⊢ Forget'
----
...
----
D', D' ⊢ Forget', Forget'
---- [alias-right](Forget')
D', D' ⊢ Forget', { forget : Self -> Forget' }
---- [cls-left](D', Self = D')
Self = D', D', D' <: Forget', { forget : D' -> D' } ⊢ Forget', { forget : Self -> Forget' }
---- [subt-left](D', D' <: Forget')
Self = D', D', D' <: Forget', Forget', { ... } ⊢ Forget', { ... }

D' ⊢ Forget'
---- [alias-right](Forget', Self = D') // is this the right place to put Self = D' assumption
Self = D', D' ⊢ { forget : Self -> Forget' }
---- [cls-left](D')
Self = D', { forget : D' -> D' } ⊢ { forget : Self -> Forget' }
---- [record-focus](forget)
Self = D', D' -> D' ⊢ Self -> Forget'
---- [function]
(1) Self = D', Self ⊢ D' // follows from substitution
(2) Self = D', D' ⊢ Forget' // need recursive subtyping assumption here

// Both <: Shallow
// Both <: Deep

// Is Self argument special?
// Can we express self types as recursive type?


type Animal = {
    mateWith(self: Self, other: Self) : Self
}

class Dog {
    mateWith(self: Dog, other: Dog) : Dog
}


a1 : Animal
a2 : Animal
a1.self == a2.self ?

a1.mateWith(a2) // not okay!


child = a1.self == a2.self ? a1.mateWith(a2) : Ungodly

f1 : Horse
f2 : Cow

f1.mateWith(f2) : Cowse

d1 : Dog
d2 : Dog
d1.self = d2.self

d1.mateWith(d2) // okay!


class C {

}

```






```verona
class C[T] where (T < A) { ...' }


type I[T] where (T < A) = { ... }


type I = ∀T. (T < A) & { ... }


C[B] ⊢ I[B]
---- [alias-right](I)
C[B] ⊢ (∀T. (T < A) & { ... })[B]
---- [appl-right]((∀T. (T < A) & { ... })[B])
C[B] ⊢ (B < A) & { ... }
---- [cls-left](C[B], Self = C[B]) // ...'' is trait type of C[B]
(B < A) & { ...'' } ⊢ (B < A) & { ... }
---- [conj-left]
(B < A), { ...'' } ⊢ (B < A) & { ... }
---- [conj-right]
(1) (B < A), { ...'' } ⊢ (B < A) // from assumption
(2) (B < A), { ...'' } ⊢ { ... } // ...


o ⊢ A < B iff
    forall o'.   o' ⊢ A   implies   o' ⊢ B

// A < B ~ Top   ∨   A < B ~ Bot

// X type variable
A < X

o, i ⊧ A < X
    forall o'.   o', i ⊧ A   implies   o', i ⊧ X

o, i 

// i map from variable names to sets of concrete types?

X < Shallow & Deep ⊢ X < Shallow

class C[T] where (T < Shallow & Deep) { ...' }


type I[T] where (T < Shallow) = { ... }


type I = ∀T. (T < Shallow) & { ... }


C[B] ⊢ I[B]
---- [alias-right](I)
C[B] ⊢ (∀T. (T < A) & { ... })[B]
---- [appl-right]((∀T. (T < Shallow) & { ... })[B])
C[B] ⊢ (B < A) & { ... }
---- [cls-left](C[B], Self = C[B]) // ...'' is trait type of C[B]
(B < Shallow & Deep) & { ...'' } ⊢ (B < Shallow) & { ... }
---- [conj-left]
(B < Shallow & Deep), { ...'' } ⊢ (B < Shallow) & { ... }
---- [conj-right]
(1) (B < Shallow & Deep), { ...'' } ⊢ (B < Shallow)
(2) (B < Shallow & Deep), { ...'' } ⊢ { ... } // ...


(1)
---- [modallogicthing]
(B < Shallow & Deep) ⊢ B => Shallow
---- [impl-right]
B < Shallow & Deep, B ⊢ Shallow
---- [subt-left](...)
B < Shallow & Deep, B, Shallow & Deep ⊢ Shallow
----
B < Shallow & Deep, B, Shallow, Deep ⊢ Shallow // from assumption

```


```haskell

f :: A -> A


f a = x where x = a

f a = let X <: U in a
```