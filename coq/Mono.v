Require Export CoqRecon.Maybe
        CoqRecon.Typ CoqRecon.EqDecInst
        Coq.micromega.Lia.

Inductive op : Set :=
| And | Or | Add | Sub | Eq | Lt.

Inductive op_typs : op -> typ -> typ -> Prop :=
| ot_and : op_typs And TBool TBool
| ot_or  : op_typs Or  TBool TBool
| ot_add : op_typs Add TNat  TNat
| ot_sub : op_typs Sub TNat  TNat
| ot_eq  : op_typs Eq  TNat  TBool
| ot_lt  : op_typs Lt  TNat  TBool.

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

Notation "'λ' x ⇒ e"
  := (Abs x e)
       (at level 35, right associativity) : term_scope.
Notation "e1 ⋅ e2"
  := (App e1 e2)
       (at level 34, left associativity) : term_scope.

Reserved Notation "g ⊨ e ∈ t" (at level 70).

Inductive typing (Γ : gamma) : term -> typ -> Prop :=
| t_bool b :
    Γ ⊨ Bool b ∈ TBool
| t_nat n :
    Γ ⊨ Nat n ∈ TNat
| t_var x τ :
    bound x τ Γ ->
    Γ ⊨ Var x ∈ τ
| t_abs x e τ τ' :
    (x ↦ τ;; Γ)%env ⊨ e ∈ τ' ->
    Γ ⊨ (λ x ⇒ e)%term ∈ (τ → τ')%typ
| t_app e1 e2 τ τ' :
    Γ ⊨ e1 ∈ (τ → τ')%typ ->
    Γ ⊨ e2 ∈ τ ->
    Γ ⊨ (e1 ⋅ e2)%term ∈ τ'
| t_cond e1 e2 e3 τ :
    Γ ⊨ e1 ∈ TBool ->
    Γ ⊨ e2 ∈ τ ->
    Γ ⊨ e3 ∈ τ ->
    Γ ⊨ Cond e1 e2 e3 ∈ τ
| t_op o e1 e2 τ τ' :
    op_typs o τ τ' ->
    Γ ⊨ e1 ∈ τ ->
    Γ ⊨ e2 ∈ τ ->
    Γ ⊨ Op o e1 e2 ∈ τ'
where "g ⊨ e ∈ t" := (typing g e t).

Section Prez.
  Local Hint Constructors op_typs : core.

  Lemma pres_op_typs : forall o τ τ',
      op_typs o τ τ' ->
      forall σ, op_typs o (σ † τ)%typ (σ † τ')%typ.
  Proof.
    intros o t t' H s; inv H; simpl; auto.
  Qed.

  Local Hint Resolve pres_op_typs : core.
  Local Hint Constructors typing : core.
  
  Theorem preservation : forall Γ e τ,
    Γ ⊨ e ∈ τ -> forall σ,
      (σ × Γ)%env ⊨ e ∈ (σ † τ)%typ.
  Proof.
    intros g e t H;
      induction H; intros s; simpl in *; eauto.
    - constructor. unfold bound, env_map in *.
      rewrite H. reflexivity.
    - constructor.
      rewrite env_map_bind; auto.
  Qed.
End Prez.

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
      ⊣ (T :: X1 ∪ X2)%set
      @ ((τ1, (τ2 → TVar T)%typ) :: C1 ∪ C2)%set
| ct_cond e1 e2 e3 τ1 τ2 τ3 X1 X2 X3 C1 C2 C3 :
    (X1 ∩ X2)%set = [] ->
    (X1 ∩ X3)%set = [] ->
    (X2 ∩ X3)%set = [] ->
    Γ ⊢ e1 ∈ τ1 ⊣ X1 @ C1 ->
    Γ ⊢ e2 ∈ τ2 ⊣ X2 @ C2 ->
    Γ ⊢ e3 ∈ τ3 ⊣ X3 @ C3 ->
    Γ ⊢ Cond e1 e2 e3 ∈ τ2
      ⊣ (X1 ∪ X2 ∪ X3)%set
      @ ((τ1,TBool) :: (τ2,τ3) :: C1 ∪ C2 ∪ C3)%set
| ct_op o e1 e2 τ1 τ2 τ τ' X1 X2 C1 C2 :
    (X1 ∩ X2)%set = [] ->
    op_typs o τ τ' ->
    Γ ⊢ e1 ∈ τ1 ⊣ X1 @ C1 ->
    Γ ⊢ e2 ∈ τ2 ⊣ X2 @ C2 ->
    Γ ⊢ Op o e1 e2 ∈ τ'
      ⊣ (X1 ∪ X2)%set
      @ ((τ,τ1) :: (τ,τ2) :: C1 ∪ C2)%set
where "g ⊢ e ∈ t ⊣ X @ C"
        := (constraint_typing g e t X C).

Section Sound.
  Local Hint Constructors op_typs : core.
  Local Hint Constructors typing : core.
  Local Hint Resolve preservation : core.
  Local Hint Resolve pres_op_typs : core.
  
  Theorem sound : forall Γ e t X C,
    Γ ⊢ e ∈ t ⊣ X @ C ->
    forall σ,
      Forall (uncurry (satisfy σ)) C ->
      (σ × Γ)%env ⊨ e ∈ (σ † t)%typ.
  Proof.
    intros g e t X C H; induction H; intros s HC; eauto.
    - apply IHconstraint_typing in HC.
      constructor. fold tsub.
      rewrite <- env_map_bind in HC.
      assumption.
    - inv HC. rewrite Forall_app in H8.
      destruct H8 as [HC1 HC2].
      unfold uncurry, satisfy in H7.
      apply IHconstraint_typing1 in HC1.
      apply IHconstraint_typing2 in HC2.
      rewrite H7 in HC1. eauto.
    - inv HC. inv H8.
      repeat rewrite Forall_app in H10.
      destruct H10 as [[HC1 HC2] HC3].
      apply IHconstraint_typing1 in HC1.
      apply IHconstraint_typing2 in HC2.
      apply IHconstraint_typing3 in HC3.
      unfold uncurry, satisfy in *; simpl in *.
      rewrite H7 in HC1. rewrite <- H9 in HC3. auto.
    - inv HC. inv H6.
      rewrite Forall_app in H8.
      destruct H8 as [HC1 HC2].
      apply IHconstraint_typing1 in HC1.
      apply IHconstraint_typing2 in HC2.
      unfold uncurry,satisfy in *.
      rewrite <- H5 in HC1; rewrite <- H7 in HC2. eauto.
  Qed.
End Sound.
