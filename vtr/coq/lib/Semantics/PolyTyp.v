Require Export CoqRecon.Util.ListEnv CoqRecon.Semantics.DeclTyping.

(** Poly-types/type-schemes. *)
Record poly : Set :=
  { pvars : list nat; ptyp : typ }.

Definition pgamma : Set := list (string * poly).

Declare Scope poly_scope.
Delimit Scope poly_scope with poly.

Notation "∀ X , t"
  := ({| pvars := X; ptyp := t |})
       (at level 50, no associativity) : poly_scope.

Open Scope poly_scope.
Open Scope set_scope.

Definition ptvars '(∀ TS, t : poly) : list nat := tvars t ∖ TS.

Definition ftv : pgamma -> list nat :=
  fold_right (fun '(x,p) => app (ptvars p)) [].

Definition pnv (t : typ) : poly :=
  {| pvars := []; ptyp := t |}.

Coercion pnv : typ >-> poly.

Definition binds_only_tvar (s : tenv) : Prop :=
  forall X t, s X = Some t -> exists Y, t = TVar Y.

Lemma combine_binds_only_tvar : forall XS YS,
    binds_only_tvar ~[XS ⟼ map TVar YS]~.
Proof.
  unfold binds_only_tvar.
  intro XS; induction XS as [| X XS IHXS];
    intros [| Y YS] Z t H; cbn in *;
      unfold "∅" in *; try discriminate.
  unfold bind in H.
  dispatch_eqdec; inv H; eauto.
Qed.

Reserved Notation "p1 ≂ p2" (at level 70, no associativity).

Definition alpha '((∀ XS, x) as p : poly) '(∀ YS, y : poly) : Prop :=
  length (uniques XS) = length (uniques YS) /\
  Forall (fun Y => Y ∉ ptvars p) YS /\
  ~[uniques XS ⟼  map TVar (uniques YS)]~ † x = y.

Notation "p1 ≂ p2" := (alpha p1 p2) : type_scope.

Section Alpha.
  Lemma tvars_sub_tvar_same : forall TS T,
    match ~[ TS ⟼ map TVar TS ]~ T with
    | Some τ => τ
    | None => T
    end = T.
  Proof.
    intro TS; induction TS as [| X XS IHXS]; intro T; cbn; auto.
    unfold bind; dispatch_eqdec; eauto.
  Qed.

  Local Hint Resolve tvars_sub_tvar_same : core.
  
  Lemma tvars_tsub_same : forall t TS,
    ~[TS ⟼  map TVar TS]~ † t = t.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intro TS; simpl; auto; f_equal; auto.
  Qed.

  Local Hint Resolve tvars_tsub_same : core.

  Lemma ptvars_same_Forall : forall XS x,
      Forall (fun Y : nat => Y ∉ ptvars (∀ XS, x)) XS.
  Proof.
    simpl; intro XS; induction XS as [| X XS IHXS];
      intro x; simpl in *; auto.
    constructor; simpl.
    - pose proof difference_Difference (tvars x) (X :: XS) as Hd.
      unfold Difference in Hd.
      intros H. firstorder.
    - rewrite Forall_forall.
      intros n HnXS Hin.
      specialize IHXS with x.
      rewrite Forall_forall in IHXS.
      specialize IHXS with n.
      apply IHXS in HnXS.
      rewrite remove_diff_cons in Hin.
      apply remove_sound in Hin. contradiction.
  Qed.

  Local Hint Resolve ptvars_same_Forall : core.
  Create HintDb alphadb.
  Local Hint Unfold Reflexive : alphadb.
  Local Hint Unfold alpha : alphadb.
  
  Lemma alpha_reflexive : Reflexive alpha.
  Proof.
    autounfold with alphadb; intros [XS x]; firstorder.
  Qed.

  Lemma not_in_free_vars_sym : forall x XS YS,
      length XS = length YS ->
      Forall (fun Y : nat => Y ∉ tvars x ∖ XS) YS ->
      Forall
        (fun Y : nat =>
           Y ∉ tvars (~[ XS ⟼ map TVar YS ]~ † x) ∖ YS) XS.
  Proof.
    intros t XS YS.
    repeat rewrite Forall_forall.
    generalize dependent YS;
      generalize dependent XS.
    induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros XS YS Hlen Hys X Hxs Hx; cbn in *; auto.
    - rewrite difference_app_l in Hys, Hx.
      rewrite in_app_iff in Hx.
      specialize IHt1 with XS YS X;
        specialize IHt2 with XS YS X.
      destruct Hx as [Ht1 | Ht2];
        [apply IHt1 in Ht1 | apply IHt2 in Ht2];
        clear IHt1 IHt2; auto;
          intros Z Hzys HZ; apply Hys in Hzys;
            rewrite in_app_iff in Hzys; auto.
    - rewrite app_nil_r in Hys.
      destruct (~[ XS ⟼ map TVar YS ]~ T)
        as [z |] eqn:Hz;
        try apply combine_binds_only_tvar in Hz as Hz';
        try destruct Hz' as [Z HZ]; subst; simpl in *.
      + rewrite app_nil_r in Hx.
        pose proof In_member_reflects Z YS as Hzys;
          inversion Hzys as [Hin Hmem | Hin Hmem]; clear Hzys;
            rewrite <- Hmem in Hx; simpl in *; try contradiction;
              destruct Hx; subst; try contradiction.
        rewrite combine_to_env_lookup in Hz.
        apply lookup_in in Hz.
        apply in_combine_r in Hz.
        rewrite in_map_iff in Hz.
        destruct Hz as (X' & HX' & Hinx); inv HX';
          contradiction.
      + pose proof In_member_reflects T YS as Htys;
          inversion Htys as [Hin Hmem | Hin Hmem]; clear Htys;
            rewrite <- Hmem in Hx; simpl in *; try contradiction;
              destruct Hx; subst; try contradiction.
        rewrite combine_to_env_lookup in Hz.
        apply lookup_not_in_domain in Hz.
        rewrite combine_map_fst, map_length, <- Hlen, Nat.min_id, firstn_all in Hz.
        contradiction.
  Qed.

  Lemma tvars_tsub_tvar_involutive : forall XS YS T,
      NoDup XS -> NoDup YS ->
      length XS = length YS ->
      Forall (fun Y : nat => Y ∉ [T] ∖ XS) YS ->
      ~[YS ⟼  map TVar XS]~
       † match ~[XS ⟼  map TVar YS]~ T with
         | Some τ => τ
         | None => T
         end = T.
  Proof.
    intros XS YS T Hndx Hndy Hlen Hfays; simpl in *.
    rewrite app_nil_r in Hfays.
    destruct (~[XS ⟼  map TVar YS]~ T)
      as [t |] eqn:Heqt;
      try apply combine_binds_only_tvar in Heqt as HOT;
      try destruct HOT as [Z HZ]; subst; simpl.
    - destruct (~[YS ⟼  map TVar XS]~ Z)
        as [t |] eqn:Heqt';
        try apply combine_binds_only_tvar in Heqt' as HOT;
        try destruct HOT as [W HW]; subst; simpl.
      + rewrite combine_to_env_lookup in Heqt.
        rewrite combine_to_env_lookup in Heqt'.
        apply lookup_in in Heqt  as HT.
        apply lookup_in in Heqt' as HZ.
        rewrite combine_map_r in HT, HZ.
        rewrite in_map_iff in HT, HZ.
        destruct HT as ((x1 & x2) & H1 & HYX);
          destruct HZ as ((x3 & x4) & H2 & HXY);
          inv H1; inv H2.
        apply in_combine_flip in HYX.
        eauto using NoDup_pair_eq_r.
      + exfalso.
        rewrite combine_to_env_lookup in Heqt, Heqt'.
        apply lookup_in in Heqt as HT.
        apply lookup_not_in with (v:=TVar T) in Heqt' as HZ.
        rewrite combine_map_r in HT, HZ.
        rewrite in_map_iff in HT, HZ.
        destruct HT as ((x1 & x2) & Huv & HYXS); inv Huv.
        apply in_combine_flip in HYXS. firstorder.
    - destruct (~[YS ⟼  map TVar XS]~ T)
        as [t |] eqn:Heqt';
        try apply combine_binds_only_tvar in Heqt' as HOT;
        try destruct HOT as [W HW]; subst; simpl; auto.
      rewrite Forall_forall in Hfays.
      rewrite combine_to_env_lookup in Heqt, Heqt'.
      apply lookup_in in Heqt' as HW.
      apply in_combine_l in HW as HW'.
      apply Hfays in HW'.
      apply lookup_not_in_domain in Heqt.
      rewrite combine_map_fst in Heqt.
      rewrite map_length, <- Hlen, Nat.min_id, firstn_all in Heqt.
      rewrite <- Not_In_member_iff in Heqt.
      rewrite Heqt in HW'; simpl in *.
      exfalso. intuition.
  Qed.

  Local Hint Resolve tvars_tsub_tvar_involutive : core.

  Lemma tvars_tsub_involutive : forall t XS YS,
      NoDup XS -> NoDup YS ->
      length XS = length YS ->
      Forall (fun Y : nat => Y ∉ tvars t ∖ XS) YS ->
      ~[ YS ⟼ map TVar XS ]~ † ~[ XS ⟼ map TVar YS ]~ † t = t.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros XS YS Hndx Hndy Hlen Hfays; simpl in *; auto.
    rewrite difference_app_l in Hfays.
    enough (Forall (fun Y : nat => Y ∉ tvars t1 ∖ XS) YS /\
            Forall (fun Y : nat => Y ∉ tvars t2 ∖ XS) YS).
    simpl; rewrite IHt1, IHt2; intuition.
    repeat rewrite Forall_forall in *.
    split; intros Z Hzys Hzd; apply Hfays in Hzys;
      rewrite in_app_iff in Hzys; auto.
  Qed.

  Local Hint Resolve tvars_tsub_involutive : core.
  Local Hint Unfold Symmetric : alphadb.
  Local Hint Resolve not_in_free_vars_sym : core.
  Local Hint Resolve uniques_nodup : core.
  
  Lemma alpha_symmetric : Symmetric alpha.
  Proof.
    autounfold with alphadb; intros [XS x] [YS y] (Hlen & Hys & Hy); subst y.
    repeat split; simpl in *; auto.
    - rewrite <- diff_uniques with (r := YS).
      rewrite <- diff_uniques with (r := XS) in Hys.
      rewrite <- uniques_Forall with (l := XS).
      rewrite <- uniques_Forall with (l := YS) in Hys; auto.
    - rewrite <- diff_uniques in Hys.
      rewrite <- uniques_Forall in Hys; auto.
  Qed.

  Local Hint Unfold Transitive : core.
  
  Lemma alpha_transitive : Transitive alpha.
  Proof.
    autounfold with *; intros [XS x] [YS y] [ZS z] Hxy Hyz.
  Abort.
End Alpha.

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
