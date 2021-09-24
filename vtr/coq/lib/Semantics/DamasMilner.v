Require Export CoqRecon.Semantics.PolyTyp CoqRecon.Semantics.DeclTyping.

Definition pgamma : Set := list (string * poly).

Definition ftv : pgamma -> list nat :=
  fold_right (fun '(x,p) => app (ptvars p)) [].

Section FtvProp.
  Local Hint Resolve eql_nil : core.
  
  Lemma eql_ftv_set_equiv : forall g g',
    g ≊ g' -> ftv g ≡ ftv g'.
  Proof.
    intro g; induction g as [| [x [TS t]] g IHg];
      intros [| [x' [TS' t']] g'] H; simpl in *.
    - reflexivity.
    - apply eql_nil in H; discriminate.
    - symmetry in H.
      apply eql_nil in H; discriminate.
    - eqdec x x'.
      + unfold eql in H; specialize H with x'; simpl in H.
        dispatch_eqdec. inv H.
        Search (_ ≡ _).
  Abort.
End FtvProp.

Reserved Notation "g ⫢ e ∴ p"
         (at level 70, no associativity).

Open Scope term_scope.

(** Damas Milner Declarative-typing system. *)
Inductive DM (Γ : pgamma) : term -> poly -> Prop :=
| DM_var x p :
    lookup x Γ = Some p ->
    Γ ⫢ x ∴ p
| DM_abs x e (τ τ' : typ) :
    ((x, pnv τ) :: Γ) ⫢ e ∴ τ' ->
    Γ ⫢ λ x ⇒ e ∴ τ → τ'
| DM_app e1 e2 (τ τ' : typ) :
    Γ ⫢ e1 ∴ τ → τ' ->
    Γ ⫢ e2 ∴ τ ->
    Γ ⫢ e1 ⋅ e2 ∴ τ'
| DM_let x e1 e2 p (τ : typ) :
    Γ ⫢ e1 ∴ p ->
    ((x, p) :: Γ) ⫢ e2 ∴ τ ->
    Γ ⫢ LetIn x e1 e2 ∴ τ
| DM_gen e XS (τ : typ) :
    Disjoint XS (ftv Γ) ->
    Γ ⫢ e ∴ τ ->
    Γ ⫢ e ∴ ∀ XS, τ
| DM_inst e (τ : typ) XS TS :
    Γ ⫢ e ∴ (∀ XS, τ) ->
    Γ ⫢ e ∴ ~[ XS ⟼  TS ]~ † τ
| DM_cond e1 e2 e3 p p' :
    p ≂ p' ->
    Γ ⫢ e1 ∴ TBool ->
    Γ ⫢ e2 ∴ p ->
    Γ ⫢ e3 ∴ p' ->
    Γ ⫢ Cond e1 e2 e3 ∴ p
| DM_op o e1 e2 τ τ' :
    op_typs o τ τ' ->
    Γ ⫢ e1 ∴ τ ->
    Γ ⫢ e2 ∴ τ ->
    Γ ⫢ Op o e1 e2 ∴ τ'
where "g ⫢ e ∴ p" := (DM g e p) : type_scope.

Section DM.
  Local Hint Constructors DM : core.
  Local Hint Resolve eql_cons : core.

  Lemma pgamma_equiv_DM : forall Γ Γ' e p,
      Γ ≊ Γ' -> Γ ⫢ e ∴ p -> Γ' ⫢ e ∴ p.
  Proof.
    intros g g' e p Hg Hgep.
    generalize dependent g'.
    induction Hgep; intros g' Hg; eauto.
    - rewrite Hg in H; auto.
    - constructor.
      unfold Disjoint, Intersection in *; auto.
      intro T; specialize H with T; simpl in *;
        split; intro HT; try contradiction.
      + rewrite H.
        destruct HT as [HTx HTg']; split; auto.
  Abort.
End DM.
