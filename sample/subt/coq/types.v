(* types for verona *)

From TLC Require Import LibSet LibTactics.

(* Module Verona. *)
Declare Scope verona_type_scope.

Ltac auto_tilde ::= try solve [auto with verona | intuition auto].
Ltac auto_star ::= try solve [eauto with verona | intuition eauto].

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
Notation "t1 && t2" := (TConj t1 t2).
Notation "t1 || t2" := (TDisj t1 t2).
Notation "c [ ts ]" := (TClass c ts).
Notation "a [ ts ]" := (TAlias a ts).
Notation "τ <{ f : [ Xs ] ts : t1 'where' t2 }>" :=
    (TTrait τ f Xs ts t1 t2) (at level 80).

Notation "'Self'" := (TSelf).
Notation "'Top'" := (TTop).
Notation "'Bot'" := (TBot).
Notation "t1 <: t2" := (TSub t1 t2) (at level 50).

(*
alias_lookup(α, t...) = A[X...]
Γ, A[t.../X...] ⊢ Δ
---- [alias-left]
Γ, α[t...] ⊢ Δ


alias_lookup(α) = A[X...]
Γ ⊢ Δ, A[t.../X...]
---- [alias-right]
Γ ⊢ Δ, α[t...]


class_lookup(c) = A, X... // A has holes with X...
Γ, Self <: c[t...], c[t...] <: Self, A[t.../X...] ⊢ Δ
---- [cls-left]
Γ, c[t...] ⊢ Δ
// what are the ramifications of having one single Self?


// type JSON example needs assumption that c[t...] <: c[t'...]
∀i. Γ, c[t...] <: c[t'...] ⊢ Δ, (tᵢ <: t'ᵢ) & (t'ᵢ <: tᵢ)
---- [cls-right]
Γ, c[t...] ⊢ Δ, c[t'...]


// up to renaming of parameters X...
Γ, τ{ ... } <: σ{ ... } ⊢ s'' <: t''
∀j.   Γ, τ{ ... } <: σ{ ... }, s'' ⊢ sⱼ <: tⱼ
Γ, τ{ ... } <: σ{ ... }, s'' ⊢ t' <: s'
---- [method]
Γ, τ{ f : [X...] t... -> t' where t''} ⊢ Δ, σ{ f : [X...] s... -> s' where s'' }
// TODO write example to illustrate this rule
*)

Open Scope verona_type_scope.
Definition sequent := set type.

Notation "Γ , t1" := (Γ \u \{ t1 }) (at level 90, left associativity).

Definition type2sequent (t: type) : sequent := \{ t }.
Coercion type2sequent : type >-> sequent.
Reserved Notation "Γ ⊢ Δ" (at level 95).
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
| SubSubLeft: forall Γ Δ A B,
    Γ ⊢ Δ, A ->
    Γ, B ⊢ Δ ->
    Γ, A <: B ⊢ Δ
| SubSubRight: forall Γ Δ A B,
    (* TODO: Define Γ* *)
    (* TODO: Can has Δ* as well? *)
    Γ(**), A ⊢ (B : type) ->
    Γ ⊢ Δ, A <: B
| SubTop: forall Γ Δ,
    Γ ⊢ Δ, Top
| SubBottom: forall Γ Δ,
    Γ, Bot ⊢ Δ
where "Γ ⊢ Δ" := (seq_sub Γ Δ).

Local Hint Constructors seq_sub : verona.

Lemma sub_exact_in : forall a Γ Δ,
    a \in (Γ: set type) ->
    a \in (Δ: set type) ->
    Γ ⊢ Δ.
Proof.
  introv Hinl Hinr.
  apply eq_union_single_remove_one in Hinl.
  apply eq_union_single_remove_one in Hinr.
  rewrite union_comm in Hinl, Hinr.
  rewrite Hinl. rewrite* Hinr.
Qed.

Lemma sub_top_in_right : forall Γ Δ,
    Top \in (Δ: set type) ->
    Γ ⊢ Δ.
Proof.
  introv Hin.
  apply eq_union_single_remove_one in Hin.
  rewrite union_comm in Hin.
  rewrite* Hin.
Qed.

Lemma sub_bot_in_left : forall Γ Δ,
    Bot \in (Γ: set type) ->
    Γ ⊢ Δ.
Proof.
  introv Hin.
  apply eq_union_single_remove_one in Hin.
  rewrite union_comm in Hin.
  rewrite* Hin.
Qed.

Ltac solve_sequent :=
  match goal with
  | _ : _ |- _ ⊢ (type2sequent ?A) => solve [apply (sub_exact_in A); set_prove]
  | |- _ ⊢ (type2sequent ?A) => solve [apply (sub_exact_in A); set_prove]
  | _ : _ |- _ ⊢ _ => solve [eapply sub_exact_in; set_prove
                            |eapply sub_top_in_right; set_prove
                            |eapply sub_bot_in_left; set_prove]
  |       |- _ ⊢ _ => solve [eapply sub_exact_in; set_prove
                            |eapply sub_top_in_right; set_prove
                            |eapply sub_bot_in_left; set_prove]
  end.

Local Hint Extern 2 => solve_sequent : verona.

Example ex_conj_elimination1 : forall Γ Δ a b,
    Γ, a && b ⊢ Δ, a.
Proof.
  auto with verona.
Qed.

Example ex_conj_elimination2 : forall Γ Δ a b,
    Γ, a && b ⊢ Δ, b.
Proof.
    auto with verona.
Qed.

Example ex_conj_introduction : forall Γ Δ a b,
    Γ, a, b ⊢ Δ, a && b.
Proof.
  auto with verona.
Qed.

Example ex_disj_introduction1 : forall Γ Δ a b,
    Γ, a ⊢ Δ, a || b.
Proof.
  auto with verona.
Qed.

Example ex_disj_introduction2 : forall Γ Δ a b,
    Γ, b ⊢ Δ, a || b.
Proof.
  auto with verona.
Qed.

Example ex_disj_elimination : forall Γ Δ a b,
    Γ, a || b ⊢ Δ, a, b.
Proof.
  auto with verona.
Qed.

Example ex_deep_ex_falso : forall Γ Δ a b c d e,
    Γ, Bot, a, b, c, d, e ⊢ Δ.
Proof.
  auto with verona.
Qed.

Example ex_deep_tauto : forall Γ Δ a b c d e,
    Γ ⊢ Δ, Top, a, b, c, d, e.
Proof.
  auto with verona.
Qed.

Example ex_sub_trans : forall Γ Δ a b c,
    Γ, a, a <: b, b <: c ⊢ Δ, a <: c.
Proof.
  auto with verona.
Qed.
