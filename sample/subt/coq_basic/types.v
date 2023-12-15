(* types for verona *)

From Coq Require Import Lists.List.
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
Notation " c [ ts ] " := (TClass c ts) (at level 30).
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
Definition sequent := list type.
Notation " Γ , t1 " := (t1 :: Γ) (at level 90, left associativity).
Notation " Γ ,, Δ " := (Δ ++ Γ) (at level 94, left associativity).

Definition type2sequent (t: type) : sequent := nil, t.
Coercion type2sequent : type >-> sequent.

Reserved Notation " Γ ⊢ Δ " (at level 95).
Inductive seq_sub : sequent -> sequent -> Prop :=
| SubConjLeft: forall Γ Δ t1 t2,
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
| SubOrderLeft: forall Γ Δ a b,
  Γ, b, a ⊢ Δ ->
  Γ, a, b ⊢ Δ
| SubOrderRight: forall Γ Δ a b,
  Γ ⊢ Δ, b, a ->
  Γ ⊢ Δ, a, b
| SubDupLeft: forall Γ Δ a,
  Γ, a, a ⊢ Δ ->
  Γ, a ⊢ Δ
| SubDupRight: forall Γ Δ a,
  Γ ⊢ Δ, a, a ->
  Γ ⊢ Δ, a
| SubDropLeft: forall Γ Δ a,
  Γ ⊢ Δ ->
  Γ, a ⊢ Δ
| SubDropRight: forall Γ Δ a,
  Γ ⊢ Δ ->
  Γ ⊢ Δ, a
where " Γ ⊢ Δ " := (seq_sub Γ Δ).


Example ex_conj_elimination2 : forall a b,
  a && b ⊢ b.
Proof.
  intros a b.
  constructor.
  constructor.
Qed.

Example ex_conj_elimination1 : forall a b,
  a && b ⊢ a.
Proof.
  intros a b.
  constructor.
  apply SubOrderLeft.
  constructor.
Qed.

(* Lemma syntactic_in_left : forall Γ1 Γ2 Δ a,
  Γ1, a ,, Γ2 ⊢ Δ, a.
Proof.
  intros Γ1 Γ2 Δ a.
  induction Γ2.
  - simpl.
    constructor.
  - simpl.
    apply SubDropLeft.
    assumption.
Qed.
    
Lemma syntactic_in_right : forall Γ Δ1 Δ2 a,
  Γ, a ⊢ Δ1, a ,, Δ2.
Proof.
  intros Γ Δ1 Δ2 a.
  induction Δ2.
  - simpl. constructor.
  - simpl. apply SubDropRight. assumption.
Qed. *)

Lemma syntactic_in_right : forall Γ Δ a,
  In a Δ -> Γ, a ⊢ Δ.
Proof.
  intros Γ Δ a.
  induction Δ.
  - intros H. simpl in H. contradiction.
  - intros H. destruct H.
    * subst. constructor.
    * apply SubDropRight. generalize H. assumption.
Qed.

Lemma syntactic_in_left : forall Γ Δ a,
  In a Γ -> Γ ⊢ Δ, a.
Proof.
  intros Γ Δ a.
  induction Γ.
  - intros H. simpl. contradiction.
  - intros H. destruct H. subst.
    * constructor.
    * apply SubDropLeft. generalize H. assumption.
Qed.

Lemma syntactic_match : forall Γ Δ a,
  In a Γ -> In a Δ -> Γ ⊢ Δ.
Proof.
  intros Γ Δ a.
  induction Γ.
  - intros H1 H2.
    simpl in H1. contradiction.
  - simpl. intros H1 H2. destruct H1.
    * subst. apply syntactic_in_right. assumption.
    * apply SubDropLeft. apply IHΓ. assumption. assumption.
Qed.
  



