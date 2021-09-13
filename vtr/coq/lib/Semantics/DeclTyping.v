Require Export CoqRecon.Syntax.Term CoqRecon.Util.EqDecInst.

Open Scope op_scope.

Inductive op_typs : op -> typ -> typ -> Prop :=
| ot_and : op_typs ∧ TBool TBool
| ot_or  : op_typs ∨ TBool TBool
| ot_add : op_typs ⨥ TNat  TNat
| ot_sub : op_typs ⨪ TNat  TNat
| ot_eq  : op_typs ≅ TNat  TBool
| ot_lt  : op_typs ⋖ TNat  TBool.

Open Scope term_scope.
Open Scope env_scope.

Reserved Notation "g ⊨ e ∴ t" (at level 70).

Inductive typing (Γ : gamma) : term -> typ -> Prop :=
| t_bool (b : bool) :
    Γ ⊨ b ∴ TBool
| t_nat (n : nat) :
    Γ ⊨ n ∴ TNat
| t_var x τ :
    bound x τ Γ ->
    Γ ⊨ x ∴ τ
| t_abs x e τ τ' :
    (x ↦ τ;; Γ) ⊨ e ∴ τ' ->
    Γ ⊨ (λ x ⇒ e) ∴ (τ → τ')
| t_app e1 e2 τ τ' :
    Γ ⊨ e1 ∴ (τ → τ') ->
    Γ ⊨ e2 ∴ τ ->
    Γ ⊨ (e1 ⋅ e2) ∴ τ'
| t_cond e1 e2 e3 τ :
    Γ ⊨ e1 ∴ TBool ->
    Γ ⊨ e2 ∴ τ ->
    Γ ⊨ e3 ∴ τ ->
    Γ ⊨ Cond e1 e2 e3 ∴ τ
| t_op o e1 e2 τ τ' :
    op_typs o τ τ' ->
    Γ ⊨ e1 ∴ τ ->
    Γ ⊨ e2 ∴ τ ->
    Γ ⊨ Op o e1 e2 ∴ τ'
| t_let x e1 e2 τ τ' :
    Γ ⊨ e1 ∴ τ ->
    (x ↦ τ;; Γ) ⊨ e2 ∴ τ' ->
    Γ ⊨ LetIn x e1 e2 ∴ τ'
where "g ⊨ e ∴ t" := (typing g e t).

Section Prez.
  Local Hint Constructors op_typs : core.

  Lemma pres_op_typs : forall o τ τ',
      op_typs o τ τ' ->
      forall σ, op_typs o (σ † τ) (σ † τ').
  Proof.
    intros o t t' H s; inv H; simpl; auto.
  Qed.

  Local Hint Resolve pres_op_typs : core.
  Local Hint Constructors typing : core.
  
  Theorem preservation : forall Γ e τ,
      Γ ⊨ e ∴ τ -> forall σ,
        (σ × Γ)%env ⊨ e ∴ (σ † τ).
  Proof.
    intros g e t H;
      induction H; intros s; simpl in *; eauto.
    - constructor. unfold bound, env_map in *.
      rewrite H. reflexivity.
    - constructor.
      rewrite env_map_bind; auto.
    - econstructor; eauto.
      rewrite env_map_bind; auto.
  Qed.
End Prez.
