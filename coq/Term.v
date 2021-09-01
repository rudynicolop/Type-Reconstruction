Require Export CoqRecon.Typ.

Inductive op : Set :=
| And | Or | Add | Sub | Eq | Lt.

Declare Scope op_scope.
Delimit Scope op_scope with op.

Notation "∧" := And (at level 0) : op_scope.
Notation "∨" := Or (at level 0) : op_scope.
Notation "⨥" := Add (at level 0) : op_scope.
Notation "⨪" := Sub (at level 0) : op_scope.
Notation "≅" := Eq (at level 0) : op_scope.
Notation "≦" := Lt (at level 0) : op_scope.

Inductive term : Set :=
| Var : string -> term
| Abs : string -> term -> term
| App : term -> term -> term
| Bool : bool -> term
| Nat : nat -> term
| Cond : term -> term -> term -> term
| Op : op -> term -> term -> term.

Declare Scope term_scope.
Delimit Scope term_scope with term.

Coercion Var : string >-> term.
Coercion Bool : bool >-> term.
Coercion Nat : nat >-> term.

Notation "'λ' x ⇒ e"
  := (Abs x e)
       (at level 35, right associativity) : term_scope.
Notation "e1 ⋅ e2"
  := (App e1 e2)
       (at level 29, left associativity) : term_scope.
(*Notation "[ e1 opp e2 ]"
  := (Op opp e1 e2)
  (at level 31, left associativity) : term_scope.*)
