Require Import Coq.Strings.String CoqRecon.Util.

Instance StringEqDec : EqDec string eq := {equiv_dec := string_dec}.

Inductive typ : Set :=
| TBool
| TNat
| TArrow : typ -> typ -> typ
| TVar : nat -> typ.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Notation "t1 → t2"
  := (TArrow t1 t2)
       (at level 30, right associativity) : typ_scope.

Fixpoint tvars (t : typ) : list nat :=
  match t with
  | TBool | TNat => []
  | TVar T => [T]
  | (t → t')%typ => tvars t ++ tvars t'
  end.

Definition Ctvars : list (typ * typ) -> list nat :=
  fold_right (fun '(l,r) acc => tvars l ++ tvars r ++ acc) [].

Inductive op : Set :=
| And | Or | Add | Sub | Eq | Lt.

Inductive term : Set :=
| Var : string -> term
| Abs : string -> term -> term
| App : term -> term -> term
| Bool : bool -> term
| Nat : nat -> term
| Cond : term -> term -> term
| Op : op -> term -> term.

Declare Scope term_scope.
Delimit Scope term_scope with term.

Notation "'λ' x ⇒ e"
  := (Abs x e)
       (at level 35, right associativity) : term_scope.
Notation "e1 ⋅ e2"
  := (App e1 e2)
       (at level 34, left associativity) : term_scope.

Definition gamma : Set := @env string typ.

Reserved Notation "g ⊢ e ∈ t ⊣ X @ C" (at level 70).

Inductive constraint_typing (Γ : gamma)
  : term -> typ -> list nat -> list (typ * typ) -> Prop :=
| ct_bool b :
    Γ ⊢ Bool b ∈ TBool ⊣ [] @ []
| ct_nat n :
    Γ ⊢ Nat n ∈ TNat ⊣ [] @ []
| ct_var x τ :
    bound x τ Γ ->
    Γ ⊢ Var x ∈ τ ⊣ [] @ []
| ct_abs x e T τ X C :
    ~ In T X ->
    (x ↦ TVar T ;; Γ)%env ⊢ e ∈ τ ⊣ X @ C ->
    Γ ⊢ (λ x ⇒ e)%term ∈ (TVar T → τ)%typ ⊣ (T :: X) @ C
| ct_app e1 e2 T τ1 τ2 X1 X2 C1 C2 :
    (X1 ∩ X2)%set = [] ->
    (X1 ∩ tvars τ2)%set = [] ->
    (X2 ∩ tvars τ1)%set = [] ->
    ~ In T (X1 ++ X2 ++ tvars τ1 ++ tvars τ2 ++ Ctvars C1 ++ Ctvars C2) ->
    Γ ⊢ e1 ∈ τ1 ⊣ X1 @ C1 ->
    Γ ⊢ e2 ∈ τ2 ⊣ X2 @ C2 ->
    Γ ⊢ (e1 ⋅ e2)%term ∈ TVar T
      ⊣ (T :: X1 ++ X2) @ ((τ1, (τ2 → TVar T)%typ) :: C1 ++ C2)
where "g ⊢ e ∈ t ⊣ X @ C"
        := (constraint_typing g e t X C).
