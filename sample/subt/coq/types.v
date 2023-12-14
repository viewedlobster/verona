(* types for verona *)

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

(*
Γ, t1, t2 ⊢ Δ
---- [conj-left]
Γ, t1 & t2 ⊢ Δ
*)

Inductive seq_sub :=
| 
.