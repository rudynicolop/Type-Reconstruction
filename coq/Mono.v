Require Import Coq.Strings.String.
Require Import CoqRecon.Util.

Inductive type : Set :=
| TBool
| TNat
| TArrow : type -> type -> type
| TVar : nat -> type.

Inductive op : Set :=
| And | Or | Add | Sub | Eq | Lt.

Inductive term : Set :=
| Var : string -> term
| Abs : string -> term
| App : term -> term -> term
| Bool : bool -> term
| Cond : term -> term -> term
| Op : op -> term -> term.

Definition gamma : Set := @env string type.

Inductive typing (g : gamma) : term -> type -> list string -> Prop -> Prop :=.
