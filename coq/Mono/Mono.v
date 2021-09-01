Require Export Coq.micromega.Lia CoqRecon.DeclTyping.

Reserved Notation "g ⊢ e ∴ t ⊣ X ≀ C" (at level 70).

Open Scope set_scope.

Inductive constraint_typing (Γ : gamma)
  : term -> typ -> list nat -> list (typ * typ) -> Prop :=
| ct_bool (b : bool) :
    Γ ⊢ b ∴ TBool ⊣ [] ≀ []
| ct_nat (n : nat) :
    Γ ⊢ n ∴ TNat ⊣ [] ≀ []
| ct_var x τ :
    bound x τ Γ ->
    Γ ⊢ x ∴ τ ⊣ [] ≀ []
| ct_abs x e T τ X C :
    T ∉ X ->
    (x ↦ TVar T ;; Γ)%env ⊢ e ∴ τ ⊣ X ≀ C ->
    Γ ⊢ (λ x ⇒ e)%term ∴ (TVar T → τ)%typ ⊣ (T :: X) ≀ C
| ct_app e1 e2 T τ1 τ2 X1 X2 C1 C2 :
    X1 ∩ X2 = [] ->
    X1 ∩ tvars τ2 = [] ->
    X2 ∩ tvars τ1 = [] ->
    T ∉ X1 ∪ X2 ∪ tvars τ1 ∪ tvars τ2 ∪ Ctvars C1 ∪ Ctvars C2 ->
    Γ ⊢ e1 ∴ τ1 ⊣ X1 ≀ C1 ->
    Γ ⊢ e2 ∴ τ2 ⊣ X2 ≀ C2 ->
    Γ ⊢ (e1 ⋅ e2)%term ∴ TVar T
      ⊣ (T :: X1 ∪ X2)
      ≀ ((τ1, (τ2 → TVar T)%typ) :: C1 ∪ C2)
| ct_cond e1 e2 e3 τ1 τ2 τ3 X1 X2 X3 C1 C2 C3 :
    X1 ∩ X2 = [] ->
    X1 ∩ X3 = [] ->
    X2 ∩ X3 = [] ->
    Γ ⊢ e1 ∴ τ1 ⊣ X1 ≀ C1 ->
    Γ ⊢ e2 ∴ τ2 ⊣ X2 ≀ C2 ->
    Γ ⊢ e3 ∴ τ3 ⊣ X3 ≀ C3 ->
    Γ ⊢ Cond e1 e2 e3 ∴ τ2
      ⊣ (X1 ∪ X2 ∪ X3)
      ≀ ((τ1,TBool) :: (τ2,τ3) :: C1 ∪ C2 ∪ C3)
| ct_op o e1 e2 τ1 τ2 τ τ' X1 X2 C1 C2 :
    X1 ∩ X2 = [] ->
    op_typs o τ τ' ->
    Γ ⊢ e1 ∴ τ1 ⊣ X1 ≀ C1 ->
    Γ ⊢ e2 ∴ τ2 ⊣ X2 ≀ C2 ->
    Γ ⊢ Op o e1 e2 ∴ τ'
      ⊣ (X1 ∪ X2)
      ≀ ((τ,τ1) :: (τ,τ2) :: C1 ∪ C2)
where "g ⊢ e ∴ t ⊣ X ≀ C"
        := (constraint_typing g e t X C).

Section Sound.
  Local Hint Constructors op_typs : core.
  Local Hint Constructors typing : core.
  Local Hint Resolve preservation : core.
  Local Hint Resolve pres_op_typs : core.
  
  Theorem sound : forall Γ e t X C,
      Γ ⊢ e ∴ t ⊣ X ≀ C ->
      forall σ,
        Forall (uncurry (satisfy σ)) C ->
        (σ × Γ)%env ⊨ e ∴ (σ † t).
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
