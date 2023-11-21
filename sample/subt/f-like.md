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

mt ::= ∀X. mt
     | t & mt_base
     | mt_base

mt_base ::= t -> mt
          | t
```


# Even more System F-like

## TODOs

* Example: Write down contravariant example here (see pic from elias)

```verona
type T
type A = A1{ f : A -> T }
type B = B1{ f : B -> T }

B ⊢ A
---- [alias-left] then [alias-right]
B1{ f : B -> T } ⊢ A1{ f : A -> T }
---- [conj-left]
B1{ f : B -> T } ⊢ A1{ f : A -> T }
---- [focus](f)
B1 <: A1, B -> T ⊢ A -> T
---- [function]
(1) B1 <: A1, A ⊢ B
(2) B1 <: A1, T ⊢ T // syntactic equality


(1)
---- [alias-left] then [alias-right]
B1 <: A1, A1{ f : A -> T } ⊢ B1{ f : B -> T } 
---- [focus](f)
B1 <: A1, A1 <: B1, A -> T ⊢ B -> T
---- [function]
(1.1) B1 <: A1, A1 <: B1, B ⊢ A
(1.2) B1 <: A1, A1 <: B1, T ⊢ T // syntactic equality


(1.1)
---- [alias-left] then [alias-right]
B1 <: A1, A1 <: B1, B1{ f : B -> T } ⊢ A1{ f : A -> T }
---- [discharge-sub](B1, B1 <: A1, A1)
```

* Example: Contravariance with multiple methods
```verona
type T
type S
type A = A1{ f : A -> T }
type B = B1{ f : B -> T } & B2{ g : B -> S }


B ⊢ A
----
...
----
B1{ f : B -> T } & B2{ g : B -> S } ⊢ A1{ f : A -> T }
---- [conj-left]
B1{ f : B -> T }, B2 { g : B -> S } ⊢ A1{ f : A -> T }
---- [focus](f)
B1 <: A1, B -> T ⊢ A -> T
---- [function]
(1) B1 <: A1, A ⊢ B
(2) B1 <: A1, T ⊢ T // trivial


(1)
----
...
----
B1 <: A1, A1{ f : A -> T } ⊢ B1{ f : B -> T } & B2{ g : B -> S } 
---- [conj-right]
(1.1) B1 <: A1, A1{ f : A -> T } ⊢ B1{ f : B -> T }
(1.2) B1 <: A1, A1{ f : A -> T } ⊢ B2{ g : B -> S }  // impossible


(1.1)
---- [focus]
B1 <: A1, A1 <: B1, A -> T ⊢ B -> T
---- [function]
(1.1.1) B1 <: A1, A1 <: B1, B ⊢ A
(1.1.2) B1 <: A1, A1 <: B1, T ⊢ T // trivial

(1.1.1)
---- [alias-right] then [alias-left] then [conj-left]
B1 <: A1, A1 <: B1, B1{ f : B -> T }, B2 { g : B -> S } ⊢ A1{ f : A -> T }
---- [discharge-sub](B1 <: A1, B1, A1)


// neither A <: B or B <: A
// A </: B: B contains another method

// B </: A: if we assume B <: A, then we should be able to use B in place of A,
// but we cannot unless A <: B as well (since B has itself in contravariant
// position, i.e. we should be able to feed an A to B.f since we can feed an A
// to A.f
```

```verona
type T
type S
type A = A1{ f : A -> T } & A2{ g : A -> S }
type B = B1{ f : B -> T } & B2{ g : B -> S }


A ⊢ B
---- [alias-right] then [alias-left]
A1{ f : A -> T } & A2{ g : A -> S } ⊢ B1{ f : B -> T } & B2{ g : B -> S }
---- [conj-left] then [conj-right]
(1) A1{ f : A -> T }, A2{ g : A -> S } ⊢ B1{ f : B -> T }
(2) A1{ f : A -> T }, A2{ g : A -> S } ⊢ B2{ g : B -> S }

(1)
---- [focus](f)
A1 <: B1, A -> T ⊢ B -> T // what if we have trait duplicates? what should we filter out during focus?
---- [function]
(1.1) A1 <: B1, B ⊢ A
(1.2) A1 <: B1, T ⊢ T // done


(1.1)
---- [alias-right] then [alias-left]
A1 <: B1, B1{ f : B -> T } & B2{ g : B -> S } ⊢ A1{ f : A -> T } & A2{ g : A -> S }
---- [conj-left] then [conj-right]
(1.1.1) A1 <: B1, B1{ f : B -> T }, B2{ g : B -> S } ⊢ A1{ f : A -> T }
(1.1.2) A1 <: B1, B1{ f : B -> T }, B2{ g : B -> S } ⊢ A2{ g : A -> S }


(1.1.1)
---- [focus](f)
A1 <: B1, B1 <: A1, B -> T ⊢ A -> T
---- [function]
(1.1.1.1) A1 <: B1, B1 <: A1, A ⊢ B
(1.1.1.2) A1 <: B1, B1 <: A1, T ⊢ T // done

(1.1.1.1)
---- [alias-right] then [alias-left] then [conj-left]
A1 <: B1, B1 <: A1, A1{ f : A -> T }, A2{ g : A -> S } ⊢ B1{ f : B -> T } & B2{ g : B -> S }
---- [conj-right]
(1.1.1.1.1) A1 <: B1, B1 <: A1, A1{ f : A -> T }, A2{ g : A -> S } ⊢ B1{ f : B -> T }
(1.1.1.1.2) A1 <: B1, B1 <: A1, A1{ f : A -> T }, A2{ g : A -> S } ⊢ B2{ g : B -> S }


(1.1.1.1.1)
---- [discharge-sub](A1, A1 <: B1, B1) // done

(1.1.1.1.2) 
---- [focus](g)
A1 <: B1, B1 <: A1, A2 <: B2, A -> S ⊢ B -> S
---- [function]
(1.1.1.1.2.1) A1 <: B1, B1 <: A1, A2 <: B2, B ⊢ A
(1.1.1.1.2.2) A1 <: B1, B1 <: A1, A2 <: B2, S ⊢ S // done

(1.1.1.1.2.1)
---- [alias-left] then [alias-right] then [conj-left] then [conj-right]
(1.1.1.1.2.1.1) A1 <: B1, B1 <: A1, A2 <: B2, B1{ f : B -> T }, B2{ g : B -> S } ⊢ A1{ f : A -> T }
(1.1.1.1.2.1.2) A1 <: B1, B1 <: A1, A2 <: B2, B1{ f : B -> T }, B2{ g : B -> S } ⊢ A2{ g : A -> S }

(1.1.1.1.2.1.1)
---- [discharge-sub](B1, B1 <: A1, A1) // done

(1.1.1.1.2.1.2)
---- [focus](g)
A1 <: B1, B1 <: A1, A2 <: B2, B2 <: A2, B -> S ⊢ A -> S
---- [function]
(1.1.1.1.2.1.2.1) A1 <: B1, B1 <: A1, A2 <: B2, B2 <: A2, A ⊢ B
(1.1.1.1.2.1.2.2) A1 <: B1, B1 <: A1, A2 <: B2, B2 <: A2, S ⊢ S // done


(1.1.1.1.2.1.2.1)
---- [alias-left] then [alias-right] then [conj-left] then [conj-right]
(1.1.1.1.2.1.2.1.1) A1 <: B1, B1 <: A1, A2 <: B2, B2 <: A2, A1{ f : A -> T }, A2{ g : A -> S } ⊢ B1{ f : B -> T }
(1.1.1.1.2.1.2.1.2) A1 <: B1, B1 <: A1, A2 <: B2, B2 <: A2, A1{ f : A -> T }, A2{ g : A -> S } ⊢ B2{ g : B -> S }


(1.1.1.1.2.1.2.1.1)
---- [discharge-sub](A1, A1 <: B1, B1) // done

(1.1.1.1.2.1.2.1.2)
---- [discharge-sub](A2, A2 <: B2, B2) // done

// the rest is similar
```
* Theory: Can we add assumptions of proven things when we backtrack?

* Example: Mutual recursion

```verona
type A = { f : B }
type B = { f : A }

A ⊢ B
```

```verona
// writing
type A = { f : S -> B }
type B = { g : T -> A }

type C = { f : S -> { g : T -> C } }

type A = { f : B }
type B = { g : A }

type C = { f : { g : C } }

type A = A1#{ f : B }
type B = B1#{ g : A }

type C = C1#{ f : C2#{ g : C } }

A ⊢ C
---- [alias-left] then [alias-right]
A1#{ f : B } ⊢ C1#{ f : C2#{ g : C } }
---- [focus](f)
A1 <: C1, B ⊢ C2#{ g : C }
---- [alias-left]
A1 <: C1, B1#{ g : A } ⊢ C2#{ g : C }
---- [focus](g)
B1 <: C2, A1 <: C1, A ⊢ C
---- [alias-left] then [alias-right]
B1 <: C2, A1 <: C1, A1#{ f : B } ⊢ C1#{ f : C2#{ g : C } }
---- [discharge-sub](A1, A1 <: C1, C2)

// is this cyclic proofs?
// we basically record steps taken with the help of assumptions A1 <: C1 etc.




C ⊢ A
---- [alias-left] then [alias-right]
C1#{ f : C2#{ g : C } } ⊢ A1#{ f : B } 
---- [focus](f)
C1 <: A1, C2#{ g : C } ⊢ B
---- [alias-right]
C1 <: A1, C2#{ g : C } ⊢ B1#{ g : A }
---- [focus](g)
C1 <: A1, C2 <: B1, C ⊢ A
---- // ... similar to above
```

* Example: Look at mutual recursion paper for examples
* Example: Multiple Self = ...
* Example: Iso-recursive failure, can our system do more?
* Example: Polymorphic type

```verona

type A = ∀X. A1[X]{
    f : X
}


class C[Y] {
    f : Y
}
=~= // equal ish
type C = ∀Y. class Cl[Y] {
    f : Y
}


o ⊧ T

o 


// can we model classes with
type C = ∀X. {
    ClsC : Bot
} & {
    f : X
}

type A = {
    f : Self -> T
}


C ⊢ A
---- [alias-right] then [alias-left]
∀Y. Cl[Y] ⊢ ∀X. A1[X]{ f : X }
---- [instansiate](Z) // must keep instansiations separate from other stuff, do we filter out everything in context that cannot be instansiated? kernel Fsub or full Fsub?
Cl[Z] ⊢ A1[Z]{ f : Z }
---- [cls-left]
Self = Cl[Z], Cl1[Z]{ f : Z } ⊢ A1[Z]{ f : Z }
---- [focus](f)
Self = Cl[Z], Z ⊢ Z
---- [discharge-syntactic](Z)


Cl1[T] <: A1[T]

Cl1[Z] <: A1[Z]

Cl1 <: A1

type A = ∀X. A1[X]{
    f : Self -> A[X]
}

class C[Y] {
    f : C[Y] -> C[Y]
}
=~=
type C = ∀Y. class Cl {
    f : C[Y]
}

C ⊢ A
---- [alias-right] then [alias-left]

// TODO how does this compare to F-bounded polymorphism? In our system we have where clauses instead
```


## syntax
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

// TODO verona language does not allow values of function type, instead functions are represented by traits
// - what do these traits look like?

// TODO we somehow want to restrict top level types to not have function form, i.e. we cannot construct values that are functions?
```



## denotation of types
```cmath
o, i ⊧ t1 | t2 iff
    o, i ⊧ t1   ∨   o, i ⊧ t2


o, i ⊧ t1 & t2 iff
    o, i ⊧ t1   ∧   o, i ⊧ t2


o, i ⊧ ∀X. t iff
    forall d.   o, i[X ↦ d] ⊧ t



o, i ⊧ C[t...] iff
    class_name(o) = C   ∧
    forall o'.   o', i ⊧ class_arg(o, i)


o, i ⊧ C[t...] iff
    class_name(o) == C   ∧
    forall o' j.   o', i ⊧ class_arg(o, j)   iff   o', i ⊧ tj
// class_arg(o, i) = ith argument to o class


o, i ⊧ Self iff
    o ∈ i[Self]

o, i ⊧ X iff
    o ∈ i[X]


o, i ⊧ α{ f : mt } iff
    m(o, f) = m   ∧   m, i[Self ↦ {o}] ⊧ mt


//o, i ⊧ { f : t } iff
//    mtype(o, f) = t'   ∧
//    forall o'.   o', o ⊧ t'   implies   o', o ⊧ t  // set i = o
//    // Self type?

```

## examples and theory crafting

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

// TODO mutually recursive types?

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