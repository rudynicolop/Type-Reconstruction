Require Export CoqRecon.Semantics.PolyTyp CoqRecon.Semantics.DeclTyping.

Definition pgamma : Set := list (string * poly).

Definition ftv : pgamma -> list nat :=
  fold_right (fun '(x,p) => app (ptvars p)) [].

Definition FTV (g : pgamma) : list nat := ftv (collapse g).

Section FtvProp.
  Local Hint Resolve Subset_union_distr_l : core.
  Local Hint Resolve Subset_union_distr_r : core.
  Local Hint Resolve Subset_reflexive : core.
  Local Hint Resolve Subset_perm_l : core.
  Local Hint Resolve Permutation_app_swap : core.
  Local Hint Resolve Subset_refl : core.
  Local Hint Resolve Subset_trans : core.
  Hint Rewrite app_assoc : core.
  
  Lemma perm_ftv : forall g g',
    Permutation g g' -> ftv g ≡ ftv g'.
  Proof.
    unfold "≡"; intros g g' Hp;
      induction Hp
      as [| [x [US u]] g g' Hgg' [IHgg' IHg'g]
          | [x [US u]] [y [VS v]] g
          | g g' g'' Hgg' [IHgg' IHg'g] Hg'g'' [IHg'g'' IHg''g']];
      simpl in *; autorewrite with core;
        intuition eauto.
  Qed.
  
  Local Hint Resolve once_eql_perm : core.
  Local Hint Resolve perm_ftv : core.

  Lemma once_eql_ftv : forall g g',
      Once g -> Once g' -> g ≊ g' -> ftv g ≡ ftv g'.
  Proof.
    eauto.
  Qed.

  Local Hint Resolve Subset_nil : core.
  
  Lemma ftv_uproot_l : forall g x, ftv (uproot x g) ⊆ ftv g.
  Proof.
    intro g; induction g as [| [x [TS t]] g IHg];
      intro y; simpl in *; auto.
    dispatch_eqdec; auto.
    apply (Subset_union []); auto.
  Qed.

  Local Hint Resolve Once_collapse : core.
  Local Hint Resolve once_eql_ftv : core.
  
  Lemma eql_FTV : forall g g',
      g ≊ g' -> FTV g ≡ FTV g'.
  Proof.
    intros g g' H.
    rewrite <- collapse_eql with (l := g) in H.
    rewrite <- collapse_eql with (l := g') in H.
    unfold FTV; auto.
  Qed.
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
    NoDup XS ->
    Disjoint XS (FTV Γ) ->
    Γ ⫢ e ∴ τ ->
    Γ ⫢ e ∴ ∀ XS, τ
| DM_inst e (τ : typ) XS ts :
    Γ ⫢ e ∴ (∀ XS, τ) ->
    Γ ⫢ e ∴ ~[ XS ⟼  ts ]~ † τ
| DM_cond e1 e2 e3 (τ : typ) :
    Γ ⫢ e1 ∴ TBool ->
    Γ ⫢ e2 ∴ τ ->
    Γ ⫢ e3 ∴ τ ->
    Γ ⫢ Cond e1 e2 e3 ∴ τ
| DM_op o e1 e2 τ τ' :
    op_typs o τ τ' ->
    Γ ⫢ e1 ∴ τ ->
    Γ ⫢ e2 ∴ τ ->
    Γ ⫢ Op o e1 e2 ∴ τ'
where "g ⫢ e ∴ p" := (DM g e p) : type_scope.

Section DM.
  Local Hint Constructors DM : core.
  Local Hint Resolve eql_cons : core.
  (*Local Hint Resolve eql_FTV : core.*)

  Lemma pgamma_equiv_DM : forall Γ Γ' e p,
      Γ ≊ Γ' -> Γ ⫢ e ∴ p -> Γ' ⫢ e ∴ p.
  Proof.
    intros g g' e p Hg Hgep.
    generalize dependent g'.
    induction Hgep as
        [ g x [TS t] Hsome
        | g x e t t' He IHe
        | g e1 e2 t t' He1 IHe1 He2 IHe2
        | g x e1 e2 [TS t] t' He1 IHe1 He2 IHe2
        | g e TS t Hnd Hdj He IHe
        | g e t XS ts He IHe
        | g e1 e2 e3 t He1 IHe1 He2 IHe2 He3 IHe3
        | g o e1 e2 t t' Ho He1 IHe1 He2 IHe2];
      intros g' Hg; eauto.
    - rewrite Hg in Hsome; auto.
    - constructor; auto.
      unfold Disjoint, Intersection in *; auto.
      intro T; specialize Hdj with T; simpl in *;
        split; intro HT; try contradiction.
      rewrite Hdj.
      destruct HT as [HTx HTg']; split; auto.
      pose proof eql_FTV _ _ Hg as [_ ?]; auto.
  Qed.

  Local Hint Constructors NoDup : core.
  
  Lemma DM_normed : forall Γ e p,
      Γ ⫢ e ∴ p -> Forall (fun '(_,p') => normed p') Γ -> normed p.
  Proof.
    intros g e p Hgep Hg;
      induction Hgep as
        [ g x [TS t] Hsome
        | g x e t t' He IHe
        | g e1 e2 t t' He1 IHe1 He2 IHe2
        | g x e1 e2 [TS t] t' He1 IHe1 He2 IHe2
        | g e TS t Hnd Hdj He IHe
        | g e t XS ts He IHe
        | g e1 e2 e3 t He1 IHe1 He2 IHe2 He3 IHe3
        | g o e1 e2 t t' Ho He1 IHe1 He2 IHe2];
      simpl in *; auto.
    rewrite Forall_forall in Hg.
    apply lookup_in in Hsome.
    firstorder.
  Qed.

  Local Hint Resolve DM_normed : core.
  
  Lemma alpha_DM : forall Γ e p p',
      normed p' ->
      Disjoint (pvars p') (FTV Γ) ->
      Forall (fun '(_,p) => normed p) Γ ->
      p ≂ p' -> Γ ⫢ e ∴ p -> Γ ⫢ e ∴ p'.
  Proof.
    unfold "≂";
      intros g e [US u] [VS v]
             Hn Hdi Hg (Hl & Hfa & Hv) Hge; subst v.
    apply DM_gen; auto; apply DM_inst.
    assert (Hnp : normed (∀ US, u)) by eauto.
    unfold normed in Hnp.
    rewrite NoDup_uniques_idem by assumption.
    assumption.
  Qed.
End DM.
