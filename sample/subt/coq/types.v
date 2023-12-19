(* types for verona *)

From TLC Require Import LibSet LibTactics.
From Coq Require Import List.

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
    method_name ->
    var_name -> (*method type start*)
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
Notation "'{' f '.:' '[' Xs ']' ts '.:' t1 'where' t2 '}'" :=
    (TTrait f Xs ts t1 t2) (at level 80).

Notation "'Self'" := (TSelf).
Notation "'Top'" := (TTop).
Notation "'Bot'" := (TBot).
Notation "t1 <: t2" := (TSub t1 t2) (at level 50).

Open Scope verona_type_scope.
Definition sequent := set type.

Notation "Γ ,, t1" := (Γ \u \{ t1 }) (at level 51, left associativity).

Definition type2sequent (t: type) : sequent := \{ t }.
Coercion type2sequent : type >-> sequent.

Local Hint Extern 1 => set_prove : verona.

Lemma sequent_dup : forall A Γ,
    A \in (Γ: set type) ->
    Γ = (Γ,, A).
Proof.
  introv Hin.
  rewrite set_in_extens_eq. intros B.
  splits*.
  introv HIn'. rewrite set_in_union_eq in HIn'.
  destruct* HIn'.
Qed.

Inductive alias_table := Aliases (lals: list (nat * type)).
Inductive class_table := Classes (lcls: list (nat * type)).

Definition class_lookup cls c := match cls with
| Classes (lcls) => List.nth_error lcls c
end.
Definition alias_lookup als a := match als with
| Aliases (lals) => List.nth_error lals a
end.

Check { 1 .: [1] ((TVar 1)::nil) .: (TVar 1) where Top }.
Inductive wf_type (cls: class_table) (als: alias_table) (mvar: var_name):
    type -> Prop :=
    | WFTDisj: forall t1 t2,
        wf_type cls als mvar t1 ->
        wf_type cls als mvar t2 ->
        wf_type cls als mvar (t1 || t2)
    | WFTConj: forall t1 t2,
        wf_type cls als mvar t1 ->
        wf_type cls als mvar t2 ->
        wf_type cls als mvar (t1 && t2)
    | WFTClass: forall c ts n tpe,
        class_lookup cls c = Some (n, tpe) ->
        length ts = n ->
        Forall (fun t => wf_type cls als mvar t) ts ->
        wf_type cls als mvar (TClass c ts)
    | WFTAlias: forall a ts n tpe,
        alias_lookup als a = Some (n, tpe) ->
        length ts = n ->
        Forall (fun t => wf_type cls als mvar t) ts ->
        wf_type cls als mvar (TAlias a ts)
    | WFTTrait: forall mname mvar_tr ts t tcond,
        Forall (fun t => wf_type cls als (mvar + mvar_tr) t) ts ->
        wf_type cls als (mvar + mvar_tr) t ->
        wf_type cls als (mvar + mvar_tr) tcond -> (* do we need syntax-check on tcond? *)
        wf_type cls als mvar ({ mname .: [ mvar_tr ] ts .: t where tcond })
    | WFTVar: forall vname,
        vname < mvar ->
        wf_type cls als mvar (TVar vname)
    | WFTSelf: wf_type cls als mvar Self (* Do we need additional checks? *)
    | WFTTop: wf_type cls als mvar Top
    | WFTBot: wf_type cls als mvar Bot
    | WFTSub: forall t1 t2,
        wf_type cls als mvar t1 ->
        wf_type cls als mvar t2 ->
        wf_type cls als mvar (t1 <: t2)
.

Reserved Notation "Γ ⊢ Δ" (at level 95).
Inductive seq_sub {cls_tbl: class_table} {als_tbl: alias_table} :
    sequent -> sequent -> Prop :=
| SubConjLeft: forall (Γ Δ:sequent) (t1 t2:type),
    Γ,, t1,, t2 ⊢ Δ ->
    Γ,, t1 && t2 ⊢ Δ
| SubConjRight: forall Γ Δ t1 t2,
    Γ ⊢ Δ,, t1 ->
    Γ ⊢ Δ,, t2 ->
    Γ ⊢ Δ,, t1 && t2
| SubDisjLeft: forall Γ Δ t1 t2,
    Γ,, t1 ⊢ Δ ->
    Γ,, t2 ⊢ Δ ->
    Γ,, t1 || t2 ⊢ Δ
| SubDisjRight: forall Γ Δ t1 t2,
    Γ ⊢ Δ,, t1,, t2 ->
    Γ ⊢ Δ,, t1 || t2
| SubSyntactic: forall Γ Δ t,
    Γ,, t ⊢ Δ,, t
| SubSubLeft: forall Γ Δ A B,
    Γ ⊢ Δ,, A ->
    Γ,, B ⊢ Δ ->
    Γ,, A <: B ⊢ Δ
| SubSubRight: forall Γ Δ A B,
    (* TODO: Define Γ* *)
    (* TODO: Can has Δ* as well? *)
    Γ(**),, A ⊢ (B : type) ->
    Γ ⊢ Δ,, A <: B
| SubTop: forall Γ Δ,
    Γ ⊢ Δ,, Top
| SubBottom: forall Γ Δ,
    Γ,, Bot ⊢ Δ
where "Γ ⊢ Δ" := (seq_sub Γ Δ).

Local Hint Constructors seq_sub : verona.

Notation "cls ; als // Γ .⊢ Δ" := (@seq_sub cls als Γ Δ) (at level 95).

Lemma sub_exact_in : forall A Γ Δ cls als,
    A \in (Γ: set type) ->
    A \in (Δ: set type) ->
    cls; als // Γ .⊢ Δ.
Proof.
  introv Hinl Hinr.
  apply eq_union_single_remove_one in Hinl.
  apply eq_union_single_remove_one in Hinr.
  rewrite union_comm in Hinl, Hinr.
  rewrite Hinl. rewrite* Hinr.
Qed.

Lemma sub_singleton_right : forall (A : type) Γ cls als,
    A \in (Γ: set type) ->
    cls; als // Γ .⊢ A.
Proof.
  introv Hin. apply* sub_exact_in.
Qed.

Lemma sub_sub_in_left : forall A B Γ Δ cls als,
    (A <: B) \in (Γ: set type) ->
    cls; als // Γ .⊢ Δ,, A ->
    cls; als // Γ,, B .⊢ Δ ->
    cls; als // Γ .⊢ Δ.
Proof.
  introv Hinl H1 H2.
  apply sequent_dup in Hinl.
  rewrite* Hinl.
Qed.

Lemma sub_sub_in_right : forall A B Γ Δ cls als,
    (A <: B) \in (Δ: set type) ->
    cls; als // Γ,, A .⊢ B ->
    cls; als // Γ .⊢ Δ.
Proof.
  introv Hinr H1.
  apply sequent_dup in Hinr.
  rewrite* Hinr.
Qed.

Lemma sub_sub_singleton_right : forall A B Γ cls als,
    cls; als // Γ,, A .⊢ (B : type) ->
    cls; als // Γ .⊢ A <: B.
Proof.
  introv H1.
  apply* sub_sub_in_right. set_prove.
Qed.

Lemma sub_parts : forall Γ Δ Γ' Δ' cls als,
    Γ' \c Γ ->
    Δ' \c Δ ->
    cls; als // Γ' .⊢ Δ' ->
    cls; als // Γ .⊢ Δ.
Proof. Abort.

Lemma sub_top_in_right : forall Γ Δ cls als,
    Top \in (Δ: set type) ->
    cls; als // Γ .⊢ Δ.
Proof.
  introv Hin.
  apply eq_union_single_remove_one in Hin.
  rewrite union_comm in Hin.
  rewrite* Hin.
Qed.

Lemma sub_bot_in_left : forall Γ Δ cls als,
    Bot \in (Γ: set type) ->
    cls; als // Γ .⊢ Δ.
Proof.
  introv Hin.
  apply eq_union_single_remove_one in Hin.
  rewrite union_comm in Hin.
  rewrite* Hin.
Qed.

Local Hint Resolve sub_exact_in : verona.
Local Hint Resolve sub_singleton_right : verona.
Local Hint Resolve sub_bot_in_left : verona.
Local Hint Resolve sub_top_in_right : verona.
Local Hint Resolve sub_sub_singleton_right : verona.

Ltac extract_sub_left :=
  match goal with
  | _ : _ |- _; _ // type2sequent (?A <: ?B),, ?t1 .⊢ _ =>
      replace (type2sequent (A <: B),, t1 : set type) with (type2sequent t1,, A <: B : set type)
      by set_prove; apply SubSubLeft
  | _ : _ |- _; _ // ?Γ,, ?A <: ?B,, ?t1 .⊢ _ =>
      replace (Γ,, A <: B,, t1 : set type) with (Γ,, t1,, A <: B : set type)
      by set_prove; apply SubSubLeft
  | _ : _ |- _; _ // ?Γ,, ?A <: ?B,, ?t1,, ?t2 .⊢ _ =>
      replace (Γ,, A <: B,, t1,, t2 : set type) with (Γ,, t1,, t2,, A <: B : set type)
      by set_prove; apply SubSubLeft
  | _ : _ |- _; _ // ?Γ,, ?A <: ?B,, ?t1,, ?t2,, ?t3 .⊢ _ =>
      replace (Γ,, A <: B,, t1,, t2,, t3 : set type) with (Γ,, t1,, t2,, t3,, A <: B : set type)
      by set_prove; apply SubSubLeft
  end.
Local Hint Extern 2 => extract_sub_left : verona.

Ltac extract_sub_right :=
  match goal with
  | _ : _ |- _; _ // _ .⊢ type2sequent (?A <: ?B) =>
      apply sub_sub_singleton_right
  | _ : _ |- _; _ // _ .⊢ type2sequent (?A <: ?B),, ?t1 =>
      replace (type2sequent (A <: B),, t1 : set type) with (type2sequent t1,, A <: B : set type)
      by set_prove; apply SubSubRight
  | _ : _ |- _; _ // _ .⊢ ?Δ,, ?A <: ?B,, ?t1 =>
      replace (Δ,, A <: B,, t1 : set type) with (Δ,, A <: B,, t1 : set type)
      by set_prove; apply SubSubRight
  | _ : _ |- _; _ // _ .⊢ ?Δ,, ?A <: ?B,, ?t1,, ?t2 =>
      replace (Δ,, A <: B,, t1,, t2 : set type) with (Δ,, A <: B,, t1,, t2 : set type)
      by set_prove; apply SubSubRight
  | _ : _ |- _; _ // _ .⊢ ?Δ,, ?A <: ?B,, ?t1,, ?t2,, ?t3 =>
      replace (Δ,, A <: B,, t1,, t2,, t3 : set type) with (Δ,, A <: B,, t1,, t2,, t3 : set type)
      by set_prove; apply SubSubRight
  end.
Local Hint Extern 1 => extract_sub_right : verona.

Ltac rotate_sequent := rewrite union_comm; repeat rewrite union_assoc.

Tactic Notation "rotate_sequent*" := rotate_sequent; auto_star.
Tactic Notation "rotate_sequent~" := rotate_sequent; auto_tilde.

Example ex_conj_elimination1 : forall Γ Δ a b cls als,
    cls; als // Γ,, a && b .⊢ Δ,, a.
Proof.
  eauto with verona.
Qed.

Example ex_conj_elimination2 : forall Γ Δ a b cls als,
    cls; als // Γ,, a && b .⊢ Δ,, b.
Proof.
  eauto with verona.
Qed.

Example ex_conj_introduction : forall Γ Δ a b cls als,
    cls; als // Γ,, a,, b .⊢ Δ,, a && b.
Proof.
  eauto with verona.
Qed.

Example ex_disj_introduction1 : forall Γ Δ a b cls als,
    cls; als // Γ,, a .⊢ Δ,, a || b.
Proof.
  eauto with verona.
Qed.

Example ex_disj_introduction2 : forall Γ Δ a b cls als,
    cls; als // Γ,, b .⊢ Δ,, a || b.
Proof.
  eauto with verona.
Qed.

Example ex_disj_elimination : forall Γ Δ a b cls als,
    cls; als // Γ,, a || b .⊢ Δ,, a,, b.
Proof.
  eauto with verona.
Qed.

Example ex_deep_ex_falso : forall Γ Δ a b c d e cls als,
    cls; als // Γ,, Bot,, a,, b,, c,, d,, e .⊢ Δ.
Proof.
  auto with verona.
Qed.

Example ex_deep_tauto : forall Γ Δ a b c d e cls als,
    cls; als // Γ .⊢ Δ,, Top,, a,, b,, c,, d,, e.
Proof.
  auto with verona.
Qed.

Example ex_sub_trans : forall Γ Δ a b c cls als,
    cls; als // Γ,, a <: b,, b <: c .⊢ Δ,, a <: c.
Proof.
  auto with verona.
Qed.

Example ex_sub_trans' : forall Γ Δ a b c cls als,
    cls; als // Γ,, b <: c,, a <: b .⊢ Δ,, a <: c.
Proof.
  auto with verona.
Qed.

Example ex_sub_trans_twice : forall Γ Δ a b c d cls als,
    cls; als // Γ,, a <: b,, b <: c,, c <: d .⊢ Δ,, a <: d.
Proof.
  auto with verona.
Qed.

Example ex_sub_trans_twice' : forall Γ Δ a b c d cls als,
    cls; als // Γ,, c <: d,, b <: c,, a <: b .⊢ Δ,, a <: d.
Proof.
  eauto 6 with verona.
Qed.

Example ex_sub_trans_thrice : forall Γ Δ a b c d e cls als,
    cls; als // Γ,, a <: b,, b <: c,, c <: d,, d <: e .⊢ Δ,, a <: e.
Proof.
  auto 6 with verona.
Qed.

Example ex_sub_trans_no_context_right : forall Γ a b c cls als,
    cls; als // Γ,, a <: b,, b <: c .⊢ a <: c.
Proof.
  auto with verona.
Qed.

Example ex_sub_trans_no_context_left : forall Δ a b c cls als,
    cls; als // type2sequent (a <: b),, b <: c .⊢ Δ,, a <: c.
Proof.
  eauto 6 with verona.
Qed.

Example ex_sub_trans_no_context : forall a b c cls als,
    cls; als // type2sequent (a <: b),, b <: c .⊢ a <: c.
Proof.
  eauto 6 with verona.
Qed.

Example ex_sub_red_herring : forall Γ Δ a b c cls als,
    cls; als // Γ,, a,, b <: c .⊢ Δ,, a,, c <: b.
Proof.
  eauto with verona.
Qed.
