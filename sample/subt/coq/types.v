(* types for verona *)

From TLC Require Import LibSet LibTactics.
From Coq Require Import List.

(* Module Verona. *)

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

(* TODO maybe change name to vtype or something.... ? *)
Inductive type : Type :=
| TDisj: type -> type -> type
| TConj: type -> type -> type
| TClass: class_name -> list type -> type
| TAlias: alias_name -> list type -> type
| TTrait:
    method_name ->
    var_name -> (* number of type parameters, TODO: make this clear... *) (*method type start*)
    list type -> (* argument types *)
    type -> (* return type *)
    type -> (* where type constraint *)    (*method type end*)
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

(************)
(* Sequents *)
(************)

Notation " a \u b " := (union a b).
Notation " a \n b " := (inter a b).
Notation " \{ a } " := (single a).

(* TODO: change name "sequent" to something else *)
Notation sequent := (set type).
Notation "Γ1 ,, Γ2" := ((Γ1 : sequent) \u (Γ2 : sequent)) (at level 51, left associativity).

Definition type2sequent (t: type) : sequent := \{ t }.
Coercion type2sequent : type >-> sequent.

(* TODO: This is too conservative. Can also have conjunctions of
constraints, aliases that define constraints, etc. *)
Inductive is_boxed: type -> Prop :=
| BoxedSub : forall t1 t2, is_boxed (t1 <: t2).

Local Hint Constructors is_boxed : verona.

Notation "[[ Γ ]]" := ((Γ : set type) \n is_boxed).

Local Hint Extern 1 => set_prove : verona.

Lemma sequent_dup : forall (A : type) (Γ : sequent),
    A \in Γ ->
    Γ = (Γ,, A).
Proof.
  introv Hin.
  rewrite set_in_extens_eq. intros B.
  splits*. introv Hin'. apply in_union_inv in Hin'. inverts* Hin'.
Qed.

(**********)
(* Tables *)
(**********)

Inductive alias_table := Aliases (lals: list (nat * type)).
Inductive class_table := Classes (lcls: list (nat * type)).

Definition class_lookup cls c :=
  match cls with
  | Classes (lcls) => List.nth_error lcls c
  end.

Definition alias_lookup als a :=
  match als with
  | Aliases (lals) => List.nth_error lals a
  end.

(*********************)
(* Well-formed types *)
(*********************)

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

Definition Forall_classes (pred : nat -> type -> Prop) (tbl: class_table) :=
  match tbl with
  | Classes lcls => Forall (fun cls => pred (fst cls) (snd cls)) lcls
  end.

Definition Forall_aliases (pred : nat -> type -> Prop) (tbl: alias_table) :=
  match tbl with
  | Aliases lals => Forall (fun als => pred (fst als) (snd als)) lals
  end.

Definition wf_tables (cls : class_table) (als: alias_table) :=
  Forall_classes (wf_type cls als) cls /\ Forall_aliases (wf_type cls als) als.

(*******************)
(* Subtyping rules *)
(*******************)

Reserved Notation "Π ; Γ ⊢ Δ" (at level 95).
Inductive seq_sub {cls_tbl: class_table} {als_tbl: alias_table} :
  type -> sequent -> sequent -> Prop :=
| SubConjLeft: forall (Π : type) (Γ Δ:sequent) (t1 t2:type),
    Π; Γ,, t1,, t2 ⊢ Δ ->
    Π; Γ,, t1 && t2 ⊢ Δ
| SubConjRight: forall Π Γ Δ (t1 t2 : type),
    Π; Γ ⊢ Δ,, t1 ->
    Π; Γ ⊢ Δ,, t2 ->
    Π; Γ ⊢ Δ,, t1 && t2
| SubDisjLeft: forall Π Γ Δ (t1 t2 : type),
    Π; Γ,, t1 ⊢ Δ ->
    Π; Γ,, t2 ⊢ Δ ->
    Π; Γ,, t1 || t2 ⊢ Δ
| SubDisjRight: forall Π Γ Δ (t1 t2 : type),
    Π; Γ ⊢ Δ,, t1,, t2 ->
    Π; Γ ⊢ Δ,, t1 || t2
| SubSyntactic: forall Π (Γ Δ : set type) (t : type),
    (t \in Γ) ->
    (t \in Δ) ->
    Π; Γ ⊢ Δ
| SubSubLeft: forall Π Γ Δ (A B : type),
    Π; Γ ⊢ Δ,, A ->
    Π; Γ,, B ⊢ Δ ->
    Π; Γ,, A <: B ⊢ Δ
| SubSubRight: forall (Π : type) Γ Δ (A B : type),
    A <: B; [[Γ]],, Π,, A ⊢ (B : type) ->
    Π; Γ ⊢ Δ,, A <: B
| SubTop: forall Π Γ Δ,
    Π; Γ ⊢ Δ,, Top
| SubBottom: forall Π Γ Δ,
    Π; Γ,, Bot ⊢ Δ
where "Π ; Γ ⊢ Δ" := (seq_sub Π Γ Δ).

Local Hint Constructors seq_sub : verona.

Notation "cls ; als // Π .; Γ .⊢ Δ" := (@seq_sub cls als Π Γ Δ) (at level 95).

(**************)
(* Automation *)
(**************)

Lemma sub_exact_in : forall A Π (Γ Δ : set type) cls als,
    A \in (Γ: set type) ->
    A \in (Δ: set type) ->
    cls; als // Π .; Γ .⊢ Δ.
Proof.
  intros.
  apply (SubSyntactic Π Γ Δ A).
  assumption. assumption.
Qed.

Lemma sub_singleton_right : forall (Π A : type) Γ cls als,
    A \in (Γ: set type) ->
    cls; als // Π .; Γ .⊢ A.
Proof.
  introv Hin. apply* sub_exact_in.
Qed.

Lemma sub_sub_in_left : forall A B Π Γ Δ cls als,
    (A <: B) \in (Γ: set type) ->
    cls; als // Π .; Γ .⊢ Δ,, A ->
    cls; als // Π .; Γ,, B .⊢ Δ ->
    cls; als // Π .; Γ .⊢ Δ.
Proof.
  introv Hinl H1 H2.
  apply sequent_dup in Hinl.
  rewrite* Hinl.
Qed.

Lemma sub_sub_in_right : forall A B (Π : type) Γ Δ cls als,
    (A <: B) \in (Δ: set type) ->
    cls; als // A <: B .; [[Γ]],, Π,, A .⊢ B ->
    cls; als // Π .; Γ .⊢ Δ.
Proof.
  introv Hinr H1.
  apply sequent_dup in Hinr.
  rewrite* Hinr.
Qed.

Lemma sub_sub_singleton_right : forall (A B Π : type) Γ cls als,
    cls; als // A <: B .; [[Γ]],, Π,, A .⊢ B ->
    cls; als // Π .; Γ .⊢ A <: B.
Proof.
  introv H1.
  apply* (sub_sub_in_right A B).
Qed.

Lemma sub_parts : forall Π Γ Δ Γ' Δ' cls als,
    Γ' \c Γ ->
    Δ' \c Δ ->
    cls; als // Π .; Γ' .⊢ Δ' ->
    cls; als // Π .; Γ .⊢ Δ.
Proof. Abort.

Lemma sub_top_in_right : forall Π Γ Δ cls als,
    Top \in (Δ: set type) ->
    cls; als // Π .; Γ .⊢ Δ.
Proof.
  introv Hin.
  apply eq_union_single_remove_one in Hin.
  rewrite union_comm in Hin.
  rewrite* Hin.
Qed.

Lemma sub_bot_in_left : forall Π Γ Δ cls als,
    Bot \in Γ ->
    cls; als // Π .; Γ .⊢ Δ.
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

Set Warnings "-cast-in-pattern".

Ltac extract_sub_left :=
  match goal with
  | _ : _ |- _; _ // _ .; type2sequent (?A <: ?B),, ?t1 .⊢ _ =>
      replace (type2sequent (A <: B),, t1) with (type2sequent t1,, A <: B)
      by set_prove; apply SubSubLeft
  | _ : _ |- _; _ // _ .; ?Γ,, ?A <: ?B,, ?t1 .⊢ _ =>
      replace (Γ,, A <: B,, t1) with (Γ,, t1,, A <: B)
      by set_prove; apply SubSubLeft
  | _ : _ |- _; _ // _ .; ?Γ,, ?A <: ?B,, ?t1,, ?t2 .⊢ _ =>
      replace (Γ,, A <: B,, t1,, t2) with (Γ,, t1,, t2,, A <: B)
      by set_prove; apply SubSubLeft
  | _ : _ |- _; _ // _ .; ?Γ,, ?A <: ?B,, ?t1,, ?t2,, ?t3 .⊢ _ =>
      replace (Γ,, A <: B,, t1,, t2,, t3) with (Γ,, t1,, t2,, t3,, A <: B)
      by set_prove; apply SubSubLeft
  end.
Local Hint Extern 2 => extract_sub_left : verona.

Ltac extract_sub_right :=
  match goal with
  | _ : _ |- _; _ // _ .; _ .⊢ type2sequent (?A <: ?B) =>
      apply sub_sub_singleton_right
  | _ : _ |- _; _ // _ .;  _ .⊢ type2sequent (?A <: ?B),, ?t1 =>
      replace (type2sequent (A <: B),, t1) with (type2sequent t1,, A <: B)
      by set_prove; apply SubSubRight
  | _ : _ |- _; _ // _ .;  _ .⊢ ?Δ,, ?A <: ?B,, ?t1 =>
      replace (Δ,, A <: B,, t1) with (Δ,, A <: B,, t1)
      by set_prove; apply SubSubRight
  | _ : _ |- _; _ // _ .;  _ .⊢ ?Δ,, ?A <: ?B,, ?t1,, ?t2 =>
      replace (Δ,, A <: B,, t1,, t2) with (Δ,, A <: B,, t1,, t2)
      by set_prove; apply SubSubRight
  | _ : _ |- _; _ // _ .;  _ .⊢ ?Δ,, ?A <: ?B,, ?t1,, ?t2,, ?t3 =>
      replace (Δ,, A <: B,, t1,, t2,, t3) with (Δ,, A <: B,, t1,, t2,, t3)
      by set_prove; apply SubSubRight
  end.
Local Hint Extern 1 => extract_sub_right : verona.

Lemma push_filter : forall Γ a b,
    [[Γ,, a <: b]] = [[Γ]],, a <: b.
Proof.
  introv. rewrite set_in_extens_eq.
  intros t. splits*.
  introv Hin. apply in_union_inv in Hin.
  inverts Hin as Hin; auto_star.
  rewrite set_in_single_eq in Hin. subst.
  apply in_inter; auto_star.
  constructors.
Qed.

Lemma push_filter_singleton : forall a b,
    [[type2sequent (a <: b)]] = type2sequent (a <: b).
Proof.
  introv. rewrite set_in_extens_eq.
  intros t. splits*.
  introv Hin.
  rewrite set_in_single_eq in Hin. subst.
  apply in_inter; auto_star.
  constructors.
Qed.

Ltac push_filter :=
  match goal with
  | _ : _ |- context[ [[_,, _ <: _]] ] => rewrite push_filter
  | _ : _ |- context[ [[type2sequent (_ <: _)]] ] => rewrite push_filter_singleton
  end.

Local Hint Extern 1 => push_filter : verona.

Ltac rotate_sequent := rewrite union_comm; repeat rewrite union_assoc.

Tactic Notation "rotate_sequent*" := rotate_sequent; auto_star.
Tactic Notation "rotate_sequent~" := rotate_sequent; auto_tilde.

Ltac syntactic_right :=
  match goal with
  | _ : _ |- _; _ // _ .; _ .⊢ type2sequent (?A) =>
      apply (SubSyntactic _ _ _ A)
  | _ : _ |- _; _ // _ .; _ .⊢ _ ,, type2sequent (?A) =>
      apply (SubSyntactic _ _ _ A)
  | _ : _ |- _; _ // _ .; _ .⊢ _ ,, type2sequent (?A) ,, _ =>
      apply (SubSyntactic _ _ _ A)
  end.
Local Hint Extern 1 => syntactic_right : verona.

(************)
(* Examples *)
(************)

(* TODO: Make these work again, probably by adding hints and
tactics for when and how to use sub_sub_in_left/right *)
Example ex_conj_elimination1 : forall Π Γ Δ a b cls als,
    cls; als // Π .; Γ,, a && b .⊢ Δ,, a.
Proof.
  eauto with verona.
Qed.

Example ex_conj_elimination2 : forall Π Γ Δ a b cls als,
    cls; als // Π .; Γ,, a && b .⊢ Δ,, b.
Proof.
  eauto with verona.
Qed.

Example ex_conj_introduction : forall Π Γ Δ (a b : type) cls als,
    cls; als // Π .; Γ,, a,, b .⊢ Δ,, a && b.
Proof.
  eauto with verona.
Qed.

Example ex_disj_introduction1 : forall Π Γ Δ (a b : type) cls als,
    cls; als // Π .; Γ,, a .⊢ Δ,, a || b.
Proof.
  eauto with verona.
Qed.

Example ex_disj_introduction2 : forall Π Γ Δ (a b : type) cls als,
    cls; als // Π .; Γ,, b .⊢ Δ,, a || b.
Proof.
  eauto with verona.
Qed.

Example ex_disj_elimination : forall Π Γ Δ a b cls als,
    cls; als // Π .; Γ,, a || b .⊢ Δ,, a,, b.
Proof.
  eauto with verona.
Qed.

Example ex_deep_ex_falso : forall Π Γ Δ a b c d e cls als,
    cls; als // Π .; Γ,, Bot,, a,, b,, c,, d,, e .⊢ Δ.
Proof.
  auto with verona.
Qed.

Example ex_deep_tauto : forall Π Γ Δ a b c d e cls als,
    cls; als // Π .; Γ .⊢ Δ,, Top,, a,, b,, c,, d,, e.
Proof.
  auto with verona.
Qed.

Example ex_sub_trans : forall Π Γ Δ a b c cls als,
    cls; als // Π .; Γ,, a <: b,, b <: c .⊢ Δ,, a <: c.
Proof.
  introv.
  apply* (sub_sub_in_right a c). repeat rewrite push_filter.
  apply* (sub_sub_in_left a b).
  apply* (sub_sub_in_left b c).
(*  auto with verona. *)
Qed.

Example ex_sub_trans' : forall Π Γ Δ a b c cls als,
    cls; als // Π .; Γ,, b <: c,, a <: b .⊢ Δ,, a <: c.
Proof.
  introv.
  apply* (sub_sub_in_right a c). repeat rewrite push_filter.
  apply* (sub_sub_in_left a b).
  apply* (sub_sub_in_left b c).
(*  auto with verona. *)
Qed.

Example ex_sub_trans_twice : forall Π Γ Δ a b c d cls als,
    cls; als // Π .; Γ,, a <: b,, b <: c,, c <: d .⊢ Δ,, a <: d.
Proof.
  introv.
  apply* (sub_sub_in_right a d). repeat rewrite push_filter.
  apply* (sub_sub_in_left a b).
  apply* (sub_sub_in_left b c).
  apply* (sub_sub_in_left c d).
(*  auto with verona. *)
Qed.

Example ex_sub_trans_twice' : forall Π Γ Δ a b c d cls als,
    cls; als // Π .; Γ,, c <: d,, b <: c,, a <: b .⊢ Δ,, a <: d.
Proof.
  introv.
  apply* (sub_sub_in_right a d). repeat rewrite push_filter.
  apply* (sub_sub_in_left a b).
  apply* (sub_sub_in_left b c).
  apply* (sub_sub_in_left c d).
(*  auto 6 with verona. *)
Qed.

Example ex_sub_trans_thrice : forall Π Γ Δ a b c d e cls als,
    cls; als // Π .; Γ,, a <: b,, b <: c,, c <: d,, d <: e .⊢ Δ,, a <: e.
Proof.
  introv.
  apply* (sub_sub_in_right a e). repeat rewrite push_filter.
  apply* (sub_sub_in_left a b).
  apply* (sub_sub_in_left b c).
  apply* (sub_sub_in_left c d).
  apply* (sub_sub_in_left d e).
(*  auto 7 with verona. *)
Qed.

Example ex_sub_trans_no_context_right : forall Π Γ a b c cls als,
    cls; als // Π .; Γ,, a <: b,, b <: c .⊢ a <: c.
Proof.
  introv.
  apply* (sub_sub_in_right a c). repeat rewrite push_filter.
  apply* (sub_sub_in_left a b).
  apply* (sub_sub_in_left b c).
(*  auto 6 with verona. *)
Qed.

Example ex_sub_trans_no_context_left : forall Π Δ a b c cls als,
    cls; als // Π .; type2sequent (a <: b),, b <: c .⊢ Δ,, a <: c.
Proof.
  introv.
  apply* (sub_sub_in_right a c). repeat rewrite push_filter. rewrite push_filter_singleton.
  apply* (sub_sub_in_left b c).
  apply* (sub_sub_in_left a b).
(*  eauto 6 with verona. *)
Qed.

Example ex_sub_trans_no_context : forall Π (a b c : type) cls als,
    cls; als // Π .; type2sequent (a <: b),, b <: c .⊢ a <: c.
Proof.
  introv.
  apply* (sub_sub_in_right a c). repeat rewrite push_filter. rewrite push_filter_singleton.
  apply* (sub_sub_in_left b c).
  apply* (sub_sub_in_left a b).
(*  eauto 6 with verona. *)
Qed.

Example ex_sub_red_herring : forall Π Γ Δ (a b c : type) cls als,
    cls; als // Π .; Γ,, a,, b <: c .⊢ Δ,, a,, c <: b.
Proof.
  introv.
  eauto with verona.
Qed.
