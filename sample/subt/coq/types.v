(* types for verona *)

From TLC Require Import LibSet LibTactics.

(* Module Verona. *)
Declare Scope verona_type_scope.

(*
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


mt ::= [X...] t... : t where t
*)

Definition class_name := nat.
Definition alias_name := nat.
Definition trait_name := nat.
Definition method_name := nat.
Definition var_name := nat.

Inductive type : Type :=
| TDisj: type -> type -> type
| TConj: type -> type -> type
| TClass: class_name -> list type -> type
| TAlias: alias_name -> list type -> type
| TTrait: 
    trait_name ->
    method_name ->
    list var_name -> (*method type start*)
    list type ->
    type ->
    type -> (*method type end*)
    type
| TVar: var_name -> type
| TSelf: type
| TTop: type
| TBot: type
| TSub: type -> type -> type
.

(* TODO options for notation level for && and || ? *)
Notation " t1 && t2 " := (TConj t1 t2).
Notation " t1 || t2 " := (TDisj t1 t2).
Notation " c [ ts ] " := (TClass c ts).
Notation " a [ ts ] " := (TAlias a ts).
Notation " τ <{ f : [ Xs ] ts : t1 'where' t2 }> " :=
    (TTrait τ f Xs ts t1 t2) (at level 80).

Notation " 'Self' " := (TSelf).
Notation " 'Top' " := (TTop).
Notation " 'Bot' " := (TBot).
Notation " t1 <: t2 " := (TSub t1 t2) (at level 50).

(*
Γ, t1, t2 ⊢ Δ
---- [conj-left]
Γ, t1 & t2 ⊢ Δ
*)

Open Scope verona_type_scope.
Definition sequent := set type.
Notation " Γ , t1 " := (Γ \u \{ t1 }) (at level 90, left associativity).

Reserved Notation " Γ ⊢ Δ " (at level 95).
Inductive seq_sub : sequent -> sequent -> Prop :=
| SubConjLeft: forall (Γ Δ:sequent) (t1 t2:type),
    Γ, t1, t2 ⊢ Δ ->
    Γ, t1 && t2 ⊢ Δ
| SubConjRight: forall Γ Δ t1 t2,
    Γ ⊢ Δ, t1 ->
    Γ ⊢ Δ, t2 ->
    Γ ⊢ Δ, t1 && t2
| SubDisjLeft: forall Γ Δ t1 t2,
    Γ, t1 ⊢ Δ ->
    Γ, t2 ⊢ Δ ->
    Γ, t1 || t2 ⊢ Δ
| SubDisjRight: forall Γ Δ t1 t2,
    Γ ⊢ Δ, t1, t2 ->
    Γ ⊢ Δ, t1 || t2
| SubSyntactic: forall Γ Δ t,
    Γ, t ⊢ Δ, t
where " Γ ⊢ Δ " := (seq_sub Γ Δ).

Definition type2sequent (t: type) : sequent := empty, t.
Coercion type2sequent : type >-> sequent.

Example ex_conj_elimination1 : forall a b,
    a && b ⊢ a.
Proof.
    intros a b.
    constructor.
    replace (\{}, a, b) with (\{}, b, a).
    - constructor.
    - set_prove.
Qed.

Example ex_conj_elimination2 : forall a b,
    a && b ⊢ b.
Proof.
    intros a b.
    constructor. constructor.
Qed.
