Require Export CoqRecon.Semantics.DamasMilner
        CoqRecon.Unify.Unify.

Reserved Notation "g ⫦ e ∴ t ⊣ X ≀ C" (at level 70).

Definition Instantiates
           (g : pgamma) '((∀ TS, t) as p : poly) (WS : list nat) : Prop :=
  length (uniques TS) = length (uniques WS) /\
  Forall (fun W => W ∉ ptvars p) WS (*/\ Disjoint WS (FTV g)*).

Definition captures (g : pgamma) (t : typ) : list nat :=
  filter (fun T => negb (member T (FTV g))) (uniques (tvars t)).

Definition Generalize (s : tenv) (g : pgamma) (t : typ) : list nat :=
  captures (s ◀ g) t.

(** Based on [Types and Programming Languages],
    as well as the Cornell CS 3110 textbook
    by Michael Clarkson:
    [https://github.com/cs3110/textbook] *)
Inductive DM_constraint (Γ : pgamma)
  : term -> typ -> list nat -> list (typ * typ) -> Prop :=
| dmc_bool (b : bool) :
    Γ ⫦ b ∴ TBool ⊣ [] ≀ []
| dmc_nat (n : nat) :
    Γ ⫦ n ∴ TNat ⊣ [] ≀ []
| dmc_abs x e (T : nat) τ χ C :
    T ∉ χ ->
    (x, ∀ [], TVar T) :: Γ ⫦ e ∴ τ ⊣ χ ≀ C ->
    Γ ⫦ λ x ⇒ e ∴ T → τ ⊣ T :: χ ≀ C
| dmc_app e1 e2 T τ1 τ2 χ1 χ2 C1 C2 :
    χ1 ∩ χ2 = [] ->
    χ1 ∩ tvars τ2 = [] ->
    χ2 ∩ tvars τ1 = [] ->
    T ∉ χ1 ∪ χ2 ∪ tvars τ1 ∪ tvars τ2 ∪ Ctvars C1 ∪ Ctvars C2 ->
    Γ ⫦ e1 ∴ τ1 ⊣ χ1 ≀ C1 ->
    Γ ⫦ e2 ∴ τ2 ⊣ χ2 ≀ C2 ->
    Γ ⫦ e1 ⋅ e2 ∴ T ⊣ T :: χ1 ∪ χ2 ≀ (τ1, τ2 → T) :: C1 ∪ C2
| dmc_cond e1 e2 e3 τ1 τ2 τ3 χ1 χ2 χ3 C1 C2 C3 :
    χ1 ∩ χ2 = [] ->
    χ1 ∩ χ3 = [] ->
    χ2 ∩ χ3 = [] ->
    Γ ⫦ e1 ∴ τ1 ⊣ χ1 ≀ C1 ->
    Γ ⫦ e2 ∴ τ2 ⊣ χ2 ≀ C2 ->
    Γ ⫦ e3 ∴ τ3 ⊣ χ3 ≀ C3 ->
    Γ ⫦ Cond e1 e2 e3 ∴ τ2 ⊣ χ1 ∪ χ2 ∪ χ3
      ≀ (τ1,TBool) :: (τ2,τ3) :: C1 ∪ C2 ∪ C3
| dmc_op o e1 e2 τ1 τ2 τ τ' χ1 χ2 C1 C2 :
    χ1 ∩ χ2 = [] ->
    op_typs o τ τ' ->
    Γ ⫦ e1 ∴ τ1 ⊣ χ1 ≀ C1 ->
    Γ ⫦ e2 ∴ τ2 ⊣ χ2 ≀ C2 ->
    Γ ⫦ Op o e1 e2 ∴ τ' ⊣ χ1 ∪ χ2 ≀ (τ,τ1) :: (τ,τ2) :: C1 ∪ C2
| dmc_var x TS WS τ :
    lookup x Γ = Some (∀ TS, τ) ->
    Instantiates Γ (∀ TS, τ) WS ->
    Γ ⫦ x ∴ ~[uniques TS ⟼  map TVar (uniques WS)]~ † τ ⊣ WS ≀ []
| dmc_let x e1 e2 τ1 τ2 χ1 χ2 C1 C2 σ :
    χ1 ∩ χ2 = [] ->
    Unify C1 σ ->
    Γ ⫦ e1 ∴ τ1 ⊣ χ1 ≀ C1 ->
    (x, ∀ (Generalize σ Γ (σ † τ1)), σ † τ1)
      :: σ ◀ Γ ⫦ e2 ∴ τ2 ⊣ χ2 ≀ C2 ->
    Γ ⫦ LetIn x e1 e2 ∴ τ2 ⊣ χ1 ∪ χ2 ≀ C1 ∪ C2
where "g ⫦ e ∴ t ⊣ X ≀ C" := (DM_constraint g e t X C) : type_scope.

Reserved Notation "g ⊢W e ∴ t ⊣ X ≀ s" (at level 70).

(** Algorithm W, as given by Luis Damas. *)
Inductive W (Γ : pgamma)
  : term -> typ -> list nat -> tenv -> Prop :=
| W_bool (b : bool) :
    Γ ⊢W b ∴ TBool ⊣ [] ≀ ∅
| W_nat (n : nat) :
    Γ ⊢W n ∴ TNat ⊣ [] ≀ ∅
| W_cond e1 e2 e3 τ1 τ2 τ3 χ1 χ2 χ3 σ σ1 σ1' σ2 σ3 :
    χ1 ∩ χ2 = [] ->
    χ1 ∩ χ3 = [] ->
    χ2 ∩ χ3 = [] ->
    Unify [(τ1,TBool)] σ1' ->
    Unify [(σ3 † τ2, τ3)] σ ->
    Γ ⊢W e1 ∴ τ1 ⊣ χ1 ≀ σ1 ->
    σ1' ‡ σ1 ◀ Γ ⊢W e2 ∴ τ2 ⊣ χ2 ≀ σ2 ->
    σ2 ‡ σ1' ‡ σ1 ◀ Γ ⊢W e3 ∴ τ3 ⊣ χ3 ≀ σ3 ->
    Γ ⊢W Cond e1 e2 e3 ∴ σ † τ3 ⊣ χ1 ∪ χ2 ∪ χ3 ≀ σ ‡ σ2 ‡ σ1' ‡ σ1
| W_op o e1 e2 τ1 τ2 τ τ' χ1 χ2 σ1 σ1' σ2 σ2' :
    χ1 ∩ χ2 = [] ->
    op_typs o τ τ' ->
    Unify [(τ,τ1)] σ1' ->
    Unify [(τ,τ2)] σ2' ->
    Γ ⊢W e1 ∴ τ1 ⊣ χ1 ≀ σ1 ->
    σ1' ‡ σ1 ◀ Γ ⊢W e2 ∴ τ2 ⊣ χ2 ≀ σ2 ->
    Γ ⊢W Op o e1 e2 ∴ τ' ⊣ χ1 ∪ χ2 ≀ σ2' ‡ σ2 ‡ σ1' ‡ σ1
| W_abs x e (T : nat) τ χ σ :
    T ∉ χ ->
    (x, ∀ [], T) :: Γ ⊢W e ∴ τ ⊣ χ ≀ σ ->
    Γ ⊢W λ x ⇒ e ∴ σ † T → τ ⊣ T :: χ ≀ σ
| W_app e1 e2 T τ1 τ2 χ1 χ2 σ σ1 σ2 :
    χ1 ∩ χ2 = [] ->
    χ1 ∩ tvars τ2 = [] ->
    χ2 ∩ tvars τ1 = [] ->
    T ∉ χ1 ∪ χ2 ∪ tvars τ1 ∪ tvars τ2 ->
    Unify [(σ2 † τ1, τ2 → T)] σ ->
    Γ ⊢W e1 ∴ τ1 ⊣ χ1 ≀ σ1 ->
    σ1 ◀ Γ ⊢W e2 ∴ τ2 ⊣ χ2 ≀ σ2 ->
    Γ ⊢W e1 ⋅ e2 ∴ σ † T ⊣ T :: χ1 ∪ χ2 ≀ σ ‡ σ2 ‡ σ1
| W_var x TS WS τ :
    lookup x Γ = Some (∀ TS, τ) ->
    Instantiates Γ (∀ TS, τ) WS ->
    Γ ⊢W x ∴ ~[uniques TS ⟼  map TVar (uniques WS)]~ † τ ⊣ WS ≀ ∅
| W_let x e1 e2 τ1 τ2 χ1 χ2 σ1 σ2 :
    χ1 ∩ χ2 = [] ->
    Γ ⊢W e1 ∴ τ1 ⊣ χ1 ≀ σ1 ->
    (x, ∀ (Generalize σ1 Γ τ1), τ1) :: σ1 ◀ Γ ⊢W e2 ∴ τ2 ⊣ χ2 ≀ σ2 ->
    Γ ⊢W LetIn x e1 e2 ∴ τ2 ⊣ χ1 ∪ χ2 ≀ σ2 ‡ σ1
where "g ⊢W e ∴ t ⊣ X ≀ s" := (W g e t X s) : type_scope.
