
(* types for verona *)

From Coq Require Import List.

Module Verona.

(*
Ltac auto_tilde ::= try solve [auto with verona | intuition auto].
Ltac auto_star ::= try solve [eauto with verona | intuition eauto].
*)

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
Definition type_params := nat.
Definition var_name := nat.
Definition method_name := nat.


(*
Another way of thinking of this "delay" of subgoals is as B-hypergraph
reachability: a cyclic hyperedge is a reachable path if all of its acyclic
predececessors are reachable.
*)

Inductive vtype : Type := 
  | TDisj : vtype -> vtype -> vtype
  | TConj : vtype -> vtype -> vtype
  | TClass : class_name -> list vtype -> vtype
  | TAlias : alias_name -> list vtype -> vtype
  | TTrait :
    method_name -> (* method name *)
    type_params -> (* no. type parameters *)
    list vtype -> (* parameter types *)
    vtype -> (* result type *)
    vtype -> (* where condition *)
    vtype
  | TVar : var_name -> vtype
  | TTop : vtype
  | TBot : vtype
  | TSub : vtype -> vtype -> vtype.

Notation "t1 && t2" := (TConj t1 t2).
Notation "t1 || t2" := (TDisj t1 t2).

Notation "c 'c[' ts ']'" := (TClass c ts) (at level 81).
Notation "a 'a[' ts ']'" := (TAlias a ts) (at level 82).
Notation "'{' f '.:' '[' Xs ']' ts '.:' t1 'where' t2 '}'" :=
    (TTrait f Xs ts t1 t2) (at level 80).

Notation "'Top'" := (TTop).
Notation "'Bot'" := (TBot).
Notation "t1 <: t2" := (TSub t1 t2) (at level 50).


(* Type collections *)

Notation vtseq := (list vtype).


Notation " Γ1 ,, Γ2 " := (Γ1 ++ Γ2) (at level 83).

Definition type2gamma (t : vtype) := t :: nil.
Coercion type2gamma : vtype >-> vtseq.

Fixpoint is_boxed (t : vtype) : bool := 
  match t with
  | TConj t1 t2 => is_boxed t1 && is_boxed t2
  | TDisj t1 t2 => is_boxed t1 && is_boxed t2
  | TSub _ _ => true
  | _ => false
  end.

Definition boxed : list vtype -> list vtype :=
  filter is_boxed.

Notation "'[[' Γ ']]'" := (boxed Γ).

Inductive pfboxed : vtype -> Prop := 
| BoxedSub : forall t1 t2, pfboxed (TSub t1 t2)
| BoxedConj : forall t1 t2,
  pfboxed t1 ->
  pfboxed t2 ->
  pfboxed (TConj t1 t2)
| BoxedDisj : forall t1 t2,
  pfboxed t1 ->
  pfboxed t2 ->
  pfboxed (TDisj t1 t2).


(**********)
(* Tables *)
(**********)

Definition vtype_table := list (nat * vtype).

Definition type_lookup := @List.nth_error (nat * vtype).

(*********************)
(* Well-formed types *)
(*********************)

Inductive vtype_is_wf (cls: vtype_table) (als: vtype_table) (mvar: var_name) :
  vtype -> Prop :=
| WFTDisj: forall t1 t2,
    vtype_is_wf cls als mvar t1 ->
    vtype_is_wf cls als mvar t2 ->
    vtype_is_wf cls als mvar (t1 || t2)
| WFTConj: forall t1 t2,
    vtype_is_wf cls als mvar t1 ->
    vtype_is_wf cls als mvar t2 ->
    vtype_is_wf cls als mvar (t1 && t2)
| WFTClass: forall c ts n tpe,
    type_lookup cls c = Some (n, tpe) ->
    length ts = n ->
    Forall (fun t => vtype_is_wf cls als mvar t) ts ->
    vtype_is_wf cls als mvar (TClass c ts)
| WFTAlias: forall a ts n tpe,
    type_lookup als a = Some (n, tpe) ->
    length ts = n ->
    Forall (fun t => vtype_is_wf cls als mvar t) ts ->
    vtype_is_wf cls als mvar (TAlias a ts)
| WFTTrait: forall mname mvar_tr ts t tcond,
    Forall (fun t => vtype_is_wf cls als (mvar + mvar_tr) t) ts ->
    vtype_is_wf cls als (mvar + mvar_tr) t ->
    vtype_is_wf cls als (mvar + mvar_tr) tcond -> (* do we need syntax-check on tcond? *)
    vtype_is_wf cls als mvar ({ mname .: [ mvar_tr ] ts .: t where tcond })
| WFTVar: forall vname,
    vname < mvar ->
    vtype_is_wf cls als mvar (TVar vname)
| WFTTop: vtype_is_wf cls als mvar Top
| WFTBot: vtype_is_wf cls als mvar Bot
| WFTSub: forall t1 t2,
    vtype_is_wf cls als mvar t1 ->
    vtype_is_wf cls als mvar t2 ->
    vtype_is_wf cls als mvar (t1 <: t2)
.

(*
Inductive wf (cls: vtype_table) (als: vtype_table) (mvar: var_name):
  vtype -> Type :=
| WFTDisj: forall t1 t2,
    wf_vtype cls als mvar t1 ->
    wf_vtype cls als mvar t2 ->
    wf_vtype cls als mvar (t1 || t2)
| WFTConj: forall t1 t2,
    wf_vtype cls als mvar t1 ->
    wf_vtype cls als mvar t2 ->
    wf_vtype cls als mvar (t1 && t2)
| WFTClass: forall c ts n tpe,
    type_lookup cls c = Some (n, tpe) ->
    length ts = n ->
    Forall (fun t => wf_vtype cls als mvar t) ts ->
    wf_vtype cls als mvar (TClass c ts)
| WFTAlias: forall a ts n tpe,
    type_lookup als a = Some (n, tpe) ->
    length ts = n ->
    Forall (fun t => wf_vtype cls als mvar t) ts ->
    wf_vtype cls als mvar (TAlias a ts)
| WFTTrait: forall mname mvar_tr ts t tcond,
    Forall (fun t => wf_vtype cls als (mvar + mvar_tr) t) ts ->
    wf_vtype cls als (mvar + mvar_tr) t ->
    wf_vtype cls als (mvar + mvar_tr) tcond -> (* do we need syntax-check on tcond? *)
    wf_vtype cls als mvar ({ mname .: [ mvar_tr ] ts .: t where tcond })
| WFTVar: forall vname,
    vname < mvar ->
    wf_vtype cls als mvar (TVar vname)
| WFTTop: wf_vtype cls als mvar Top
| WFTBot: wf_vtype cls als mvar Bot
| WFTSub: forall t1 t2,
    wf_vtype cls als mvar t1 ->
    wf_vtype cls als mvar t2 ->
    wf_vtype cls als mvar (t1 <: t2)
.*)

(* TODO: well-formedness of types should include monotonicity? *)

Definition Forall_vtype_table (pred : nat -> vtype -> Prop) (tbl: vtype_table) :=
  Forall (fun cls => pred (fst cls) (snd cls)) tbl.

Definition wf_tables (cls : vtype_table) (als: vtype_table) :=
  Forall_vtype_table (vtype_is_wf cls als) cls /\
  Forall_vtype_table (vtype_is_wf cls als) als.

Module Subtyping.
Parameter clst : vtype_table.
Parameter alst : vtype_table.
Parameter wf : wf_tables clst alst.
(*******************)
(* Subtyping rules *)
(*******************)

(*
how do we prove that a function is total?
*)

  (*
Fixpoint vt_subst_tpe (ts : list vtype) (t : vtype) : option vtype :=
  match t with
  | t1 && t2 => (vt_subst_tpe ts t1) && (vt_subst_tpe ts t2)
  | t1 || t2 => (vt_subst_tpe ts t1) || (vt_subst_tpe t2)
  | c c[ ts' ] => c c[ map (vt_subst_tpe ts) ts' ]
  | a a[ ts' ] => a a[ map (vt_subst_tpe ts) ts' ]

Definition vt_subst_als (als : alias_name) (ts : list vtype) : option vtype :=
  match type_lookup alst als with
  | Some (n, t) => vt_subst_tpe_ts t ts
  | _ => None
  end.

Fixpoint vt_subst_t () (t : vtype)
  *)

Record wf_vtype n : Type := mk_wf_vtype
{ t : vtype
; is_wf : vtype_is_wf clst alst n t
}.

Lemma wf_vtype_construct : forall n t, 
    vtype_is_wf clst alst n t -> wf_vtype n.
Proof.
  intros n t wf_pf.
  apply (mk_wf_vtype n t wf_pf).
Defined.

Lemma type_lookup_implies_In (ttbl : vtype_table) : forall n vt c,
  type_lookup ttbl c = Some (n, vt) -> In (n, vt) ttbl.
Proof.
  intros.
  generalize dependent ttbl.
  induction c.
  - intros. destruct ttbl; simpl in H.
    * discriminate.
    * inversion H.
      simpl. left. reflexivity.
  - intros. destruct ttbl.
    * simpl in H. discriminate.
    * simpl in H. apply IHc in H.
      simpl. right. assumption.
Defined.

Lemma wf_vtype_class_is_lookupable : forall n c ts,
  vtype_is_wf clst alst n (c c[ts]) -> exists n' t', type_lookup clst c = Some (n', t') /\ vtype_is_wf clst alst n' t'.
Proof.
  intros n c ts wf_pf.
  inversion wf_pf.
  subst.
  exists (length ts).
  exists tpe.
  split.
  - assumption.
  - destruct wf as [wf_clss wf_alss].
    unfold Forall_vtype_table in wf_clss.
    apply type_lookup_implies_In in H1.
    rewrite Forall_forall in wf_clss.
    apply wf_clss in H1.
    simpl in H1.
    assumption.
Defined.

Definition wf_class_lookup {n: var_name} c ts (wf : vtype_is_wf clst alst n (c c[ts])) : wf_vtype n.
Proof.



Reserved Notation "Π ; Γ ⊢ Δ" (at level 95).
Inductive seq_sub : vtype -> vtseq -> vtseq -> Prop :=
| SubConjLeft : forall (Π : vtype) (Γ Δ:vtseq) (t1 t2:vtype),
  Π; t1,, t2,, Γ ⊢ Δ ->
  Π; t1 && t2,, Γ ⊢ Δ
| SubConjRight : forall Π Γ Δ (t1 t2 : vtype),
  Π; Γ ⊢ t1,, Δ ->
  Π; Γ ⊢ t2,, Δ ->
  Π; Γ ⊢ t1 && t2,, Δ
| SubDisjLeft : forall Π Γ Δ (t1 t2 : vtype),
  Π; t1,, Γ ⊢ Δ ->
  Π; t2,, Γ ⊢ Δ ->
  Π; t1 || t2,, Γ ⊢ Δ
| SubDisjRight : forall Π Γ Δ (t1 t2 : vtype),
  Π; Γ ⊢ t1,, t2,, Δ ->
  Π; Γ ⊢ t1 || t2,, Δ
| SubSyntactic: forall Π (Γ Δ : vtseq) (t : vtype),
  Π; t,, Γ ⊢ t,, Δ
| SubSubLeft : forall Π Γ Δ (A B : vtype),
  Π; Γ ⊢ A,, Δ ->
  Π; B,, Γ ⊢ Δ ->
  Π; A <: B,, Γ ⊢ Δ
| SubSubRight : forall (Π : vtype) Γ Δ (A B : vtype),
  A <: B; A,, Π,, [[Γ]] ⊢ B ->
  Π; Γ ⊢ A <: B,, Δ
| SubTop : forall Π Γ Δ,
  Π; Γ ⊢ Top,, Δ
| SubBottom : forall Π Γ Δ,
  Π; Bot,, Γ ⊢ Δ
| SubAliasLeft : forall Π Γ Δ als ts,
  Π; (subts als ts),, Γ ⊢ Δ ->
  Π; als a[ ts ],, Γ ⊢ Δ
where "Π ; Γ ⊢ Δ" := (seq_sub Π Γ Δ).

Local Hint Constructors seq_sub : verona.



End Subtyping.

End Verona.
