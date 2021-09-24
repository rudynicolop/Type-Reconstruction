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
    intros XS x. rewrite Forall_forall.
    intros X Hxxs Hxptv; simpl in *.
    pose proof difference_Difference (tvars x) XS as Hd.
    unfold Difference in Hd.
    rewrite Hd in Hxptv. firstorder.
  Qed.

  Local Hint Resolve ptvars_same_Forall : core.
  Create HintDb alphadb.
  Local Hint Unfold Reflexive : alphadb.
  Local Hint Unfold alpha : alphadb.
  
  Lemma alpha_reflexive : Reflexive alpha.
  Proof.
    autounfold with alphadb; intros [XS x]; firstorder.
  Qed.

  Lemma typ_in_tvars_subset : forall t ts,
      t ∈ ts -> tvars t ⊆ flat_map tvars ts.
  Proof.
    intros t ts Htts T HT.
    apply in_split in Htts as (ts1 & ts2 & Hts); subst.
    rewrite flat_map_app, in_app_iff; simpl.
    intuition.
  Qed.

  Lemma tvars_combine_to_env_equiv : forall t TS ts,
      tvars (~[TS ⟼  ts]~ † t) ≡
            let (TS',ts') := separate ~[TS ⟼  ts]~ (tvars t) in
            TS' ∪ flat_map tvars ts'.
  Proof.
    unfold "≡".
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros TS ts; simpl in *.
    - firstorder.
    - firstorder.
    - rewrite separate_app.
      specialize IHt1 with TS ts; destruct IHt1 as [IH1l IH1r].
      specialize IHt2 with TS ts; destruct IHt2 as [IH2l IH2r].
      destruct (separate ~[ TS ⟼ ts ]~ (tvars t1)) as [TS1' ts1'] eqn:Hsep1.
      destruct (separate ~[ TS ⟼ ts ]~ (tvars t2)) as [TS2' ts2'] eqn:Hsep2.
      rewrite flat_map_app.
      split; [clear IH1r IH2r | clear IH1l IH2l].
      + intros X. repeat rewrite in_app_iff.
        intros [HX | HX];
          try apply IH1l in HX; try apply IH2l in HX;
            repeat rewrite in_app_iff in HX; intuition.
      + intros X; pose proof IH1r X as IH1;
          pose proof IH2r X as IH2; clear IH1r IH2r.
        repeat rewrite in_app_iff in *.
        intuition.
    - destruct (~[ TS ⟼ ts ]~ T) as [t |] eqn:Heqt; simpl.
      + rewrite app_nil_r. firstorder.
      + firstorder.
  Qed.

  Lemma tsub_tvars_subset : forall t XS YS,
      flat_map tvars (filtermap ~[XS ⟼  map TVar YS]~ (tvars t)) ⊆ YS.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros XS YS; simpl in *.
    - firstorder.
    - firstorder.
    - rewrite filtermap_app, flat_map_app.
      rewrite <- Subset_extra_r.
      eauto using Subset_union.
    - rewrite app_nil_r.
      destruct (~[ XS ⟼ map TVar YS ]~ T) as [y |] eqn:Hy;
        try apply combine_binds_only_tvar in Hy as Hy';
        try destruct Hy' as [Y HY]; subst; simpl in *.
      + rewrite combine_to_env_lookup in Hy.
        apply lookup_in, in_combine_r in Hy.
        rewrite in_map_iff in Hy.
        destruct Hy as (? & HxY & HYYS); inv HxY.
        intros X HX; simpl in *.
        destruct HX; subst; try contradiction; auto.
      + firstorder.
  Qed.
  
  Lemma not_in_free_vars_sym : forall x XS YS,
      length XS = length YS ->
      Forall (fun Y : nat => Y ∉ tvars x ∖ XS) YS ->
      Forall
        (fun Y : nat =>
           Y ∉ tvars (~[ XS ⟼ map TVar YS ]~ † x) ∖ YS) XS.
  Proof.
    intros t XS YS Hxyl.
    repeat rewrite Forall_forall.
    intros Hff X Hxxs Hys.
    pose proof difference_Difference
         (tvars (~[ XS ⟼ map TVar YS ]~ † t)) YS as Hd.
    unfold Difference in Hd; rewrite Hd in Hys; clear Hd.
    destruct Hys as [Ht Hxys].
    apply tvars_combine_to_env_equiv in Ht.
    destruct (separate ~[ XS ⟼ map TVar YS ]~ (tvars t))
      as [XS' ys'] eqn:Hsep.
    assert (HXXS : exists y, ~[XS ⟼  map TVar YS]~ X = Some y).
    { rewrite combine_to_env_lookup.
      apply in_domain_lookup.
      rewrite combine_map_fst, map_length,
      <- Hxyl, Nat.min_id, firstn_all; assumption. }
    destruct HXXS as [y Hy];
      apply combine_binds_only_tvar in Hy as Hy';
      destruct Hy' as [Y HY]; subst.
    rewrite in_app_iff in Ht. destruct Ht as [Ht | Ht].
    - pose proof in_dec Nat.eq_dec X (tvars t) as [HXt | HXt].
      + pose proof not_in_fst_separate _ _ _ _ Hy HXt as Hnifs.
        rewrite Hsep in Hnifs; simpl in *. contradiction.
      + apply f_equal with (f := fst) in Hsep; simpl in *; subst XS'.
        apply in_fst_separate_in_orig in Ht; contradiction.
    - apply f_equal with (f := snd) in Hsep; simpl in *.
      rewrite separate_filtermap in Hsep; subst ys'.
      apply tsub_tvars_subset in Ht. contradiction.
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
    rewrite IHt1, IHt2; intuition.
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
    autounfold with alphadb;
      intros [XS x] [YS y] (Hlen & Hys & Hy); subst y; simpl in *.
    rewrite <- diff_uniques with (r := YS).
    rewrite <- diff_uniques with (r := XS) in Hys.
    rewrite <- uniques_Forall with (l := XS).
    rewrite <- uniques_Forall with (l := YS) in Hys.
    repeat split; simpl in *; auto.
  Qed.

  Lemma not_in_free_vars_trans : forall t XS YS ZS,
      length XS = length YS -> length YS = length ZS ->
      Forall (fun Y => Y ∉ tvars t ∖ XS) YS ->
      Forall
        (fun Z =>
           Z ∉ tvars (~[XS ⟼  map TVar YS]~ † t) ∖ YS) ZS ->
      Forall (fun Z => Z ∉ tvars t ∖ XS) ZS.
  Proof.
    intros t XS YS ZS Hxyl Hyzl Hfaxsys Hfayszs.
    rewrite Forall_forall in *.
    intros Z Hzzs Hzd.
    pose proof difference_Difference (tvars t) XS as Hd.
    unfold Difference in Hd; rewrite Hd in Hzd; clear Hd.
    destruct Hzd as [Hzt Hzxs].
    apply Hfayszs in Hzzs as Hz'.
    pose proof tvars_combine_to_env_equiv t XS (map TVar YS) as Heqv.
    destruct (separate ~[ XS ⟼ map TVar YS ]~ (tvars t)) as [XS' ys'] eqn:Hsepxy.
    assert (Hzxsnone : ~[ XS ⟼ map TVar YS ]~ Z = None).
    { rewrite combine_to_env_lookup.
      apply not_in_domain_lookup.
      rewrite combine_map_fst, map_length,
      <- Hxyl, Nat.min_id, firstn_all; assumption. }
    pose proof in_fst_separate _ _ _ Hzxsnone Hzt as Hzinfs.
    pose proof difference_Difference
         (tvars (~[ XS ⟼ map TVar YS ]~ † t)) YS as Hd.
    unfold Difference in Hd; rewrite Hd in Hz'; clear Hd.
    apply Decidable.not_and in Hz' as [Hz' | Hz'].
    - apply Hz'. destruct Heqv as [_ Heqvr].
      apply Heqvr. rewrite in_app_iff.
      apply f_equal with (f:=fst) in Hsepxy.
      simpl in *; subst XS'; auto.
    - apply Decidable.not_not in Hz'.
      + apply Hfaxsys in Hz' as Hztxs.
        apply Hztxs.
        pose proof difference_Difference (tvars t) XS as Hd.
        unfold Difference in Hd; rewrite Hd.
        intuition.
      + unfold Decidable.decidable.
        pose proof in_dec Nat.eq_dec Z YS; intuition.
    - unfold Decidable.decidable.
      pose proof in_dec Nat.eq_dec Z
           (tvars (~[ XS ⟼ map TVar YS ]~ † t)); intuition.
  Qed.
  
  Lemma tsub_tvars_tvar_compose : forall XS YS ZS T,
      NoDup XS -> NoDup YS -> NoDup ZS ->
      length XS = length YS -> length YS = length ZS ->
      Forall (fun Y : nat => Y ∉ [T] ∖ XS) YS ->
      Forall
        (fun Z : nat =>
           Z ∉ tvars match ~[ XS ⟼ map TVar YS ]~ T with
                     | Some τ => τ
                     | None => T
                     end ∖ YS) ZS ->
      match ~[ XS ⟼ map TVar ZS ]~ T with
      | Some τ => τ
      | None => T
      end =
      ~[ YS ⟼ map TVar ZS ]~ †
       match ~[ XS ⟼ map TVar YS ]~ T with
       | Some τ => τ
       | None => T
       end.
  Proof.
    intros XS YS ZS T Hndx Hndy Hndz Hxyl Hyzl Hxys Hyzs; simpl in *.
    rewrite app_nil_r in Hxys.
    destruct (~[ XS ⟼ map TVar YS ]~ T) as [y |] eqn:Heqy;
      try apply combine_binds_only_tvar in Heqy as HOT;
      try destruct HOT as [YY HYY]; subst; simpl in *.
    - rewrite app_nil_r in Hyzs.
      rewrite combine_to_env_lookup in Heqy.
      apply lookup_in in Heqy as Hliy.
      apply in_combine_l in Hliy.
      assert (HTmf : T ∈ map fst (combine XS (map TVar ZS))).
      { rewrite combine_map_fst, map_length,
        <- Hyzl, <- Hxyl, Nat.min_id, firstn_all; assumption. }
      apply in_domain_lookup in HTmf as [z' Hz'].
      rewrite <- combine_to_env_lookup in Hz'.
      apply combine_binds_only_tvar in Hz' as HZ';
        rewrite Hz'; destruct HZ' as [Z' HZ']; subst.
      apply lookup_in_image in Heqy as Himagey.
      rewrite combine_map_r,map_map,in_map_iff in Himagey.
      destruct Himagey as ((X' & Y') & HY' & HX'in); simpl in *; inv HY'.
      apply lookup_in in Heqy as Heqy'.
      rewrite combine_map_r,in_map_iff in Heqy'.
      destruct Heqy' as ((? & ?) & HeqTYY & Hinxsys);
        simpl in *; inv HeqTYY.
      assert (X' = T) by eauto using NoDup_pair_eq_l; subst; clear HX'in.
      apply in_combine_r in Hinxsys as Hinys.
      assert (Hinysdom : YY ∈ map fst (combine YS (map TVar ZS))).
      { rewrite combine_map_fst, map_length,
        <- Hyzl, Nat.min_id, firstn_all; assumption. }
      apply in_domain_lookup in Hinysdom as [z Hz].
      rewrite <- combine_to_env_lookup in Hz.
      apply combine_binds_only_tvar in Hz as Hz''.
      destruct Hz'' as [ZZ HZZ]. inv HZZ.
      rewrite Hz.
      rewrite combine_to_env_lookup in Hz',Hz.
      apply lookup_in in Hz',Hz.
      rewrite combine_map_r, in_map_iff in Hz',Hz.
      destruct Hz' as ((? & ?) & HeqTZ' & Hinxszs);
        destruct Hz as ((? & ?) & HeqYYZZ & Hinyszs);
        simpl in *. inv HeqTZ'; inv HeqYYZZ.
      eauto using nodup_triple_eq_r.
    - rewrite combine_to_env_lookup in Heqy.
      apply lookup_not_in_domain in Heqy as Hnindomxs.
      rewrite combine_map_fst,map_length,
      <- Hxyl,Nat.min_id,firstn_all in Hnindomxs.
      assert (Hnindomxszs: T ∉ map fst (combine XS (map TVar ZS))).
      { rewrite combine_map_fst,map_length.
        replace (length ZS) with (length XS) by lia.
        rewrite Nat.min_id, firstn_all; assumption. }
      apply not_in_domain_lookup in Hnindomxszs.
      rewrite combine_to_env_lookup at 1.
      rewrite Hnindomxszs.
      destruct (~[YS ⟼ map TVar ZS]~ T) as [z |] eqn:Heqz;
      try apply combine_binds_only_tvar in Heqz as HOT;
      try destruct HOT as [ZZ HZZ]; subst; simpl in *; auto.
      exfalso.
      repeat rewrite Forall_forall in *.
      rewrite combine_to_env_lookup in Heqz.
      apply lookup_in in Heqz.
      rewrite combine_map_r, in_map_iff in Heqz.
      destruct Heqz as ((? & ?) & HTZZ & Hinyszs); simpl in *; inv HTZZ.
      apply in_combine_l, Hxys in Hinyszs.
      rewrite <- Not_In_member_iff in Hnindomxs.
      rewrite Hnindomxs in Hinyszs; simpl in *.
      intuition.
  Qed.

  Local Hint Resolve tsub_tvars_tvar_compose : core.
  
  Lemma tvars_tsub_compose : forall t XS YS ZS,
      NoDup XS -> NoDup YS -> NoDup ZS ->
      length XS = length YS -> length YS  = length ZS ->
      Forall (fun Y => Y ∉ tvars t ∖ XS) YS ->
      Forall (fun Z => Z ∉ tvars (~[XS ⟼  map TVar YS]~ † t) ∖ YS) ZS ->
      ~[XS ⟼  map TVar ZS]~ † t =
      ~[YS ⟼  map TVar ZS]~ † ~[XS ⟼  map TVar YS]~ † t.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros XS YS ZS Hndx Hndy Hndz Hxyl Hyzl Hxys Hyzs;
      simpl in *; auto.
    rewrite difference_app_l in Hxys, Hyzs.
    enough (Forall (fun Y => Y ∉ tvars t1 ∖ XS) YS /\
            Forall (fun Y => Y ∉ tvars t2 ∖ XS) YS /\
            Forall
              (fun Z =>
                 Z ∉ tvars (~[ XS ⟼ map TVar YS ]~ † t1) ∖ YS) ZS /\
            Forall
              (fun Z =>
                 Z ∉ tvars (~[ XS ⟼ map TVar YS ]~ † t2) ∖ YS) ZS).
    rewrite IHt1 with (YS := YS), IHt2 with (YS := YS); intuition.
    repeat rewrite Forall_forall in *.
    repeat split; intros W Hws Hwd;
      try apply Hxys in Hws;
      try apply Hyzs in Hws;
      rewrite in_app_iff in Hws; auto.
  Qed.

  Local Hint Resolve not_in_free_vars_trans : core.
  Local Hint Resolve tvars_tsub_compose : core.
  Local Hint Unfold Transitive : core.
  
  Lemma alpha_transitive : Transitive alpha.
  Proof.
    autounfold with alphadb;
      intros [XS x] [YS y] [ZS z]
             (Hxylen & Hfays & Hy) (Hyzlen & Hfazs & Hz).
    subst y; subst z; simpl in *.
    rewrite <- diff_uniques with (r := XS).
    rewrite <- diff_uniques with (r := XS) in Hfays.
    rewrite <- diff_uniques with (r := YS) in Hfazs.
    rewrite <- uniques_Forall with (l := ZS).
    rewrite <- uniques_Forall with (l := YS) in Hfays.
    rewrite <- uniques_Forall with (l := ZS) in Hfazs.
    repeat split; eauto; try lia.
  Qed.

  Local Hint Resolve alpha_reflexive : core.
  Local Hint Resolve alpha_symmetric : core.
  Local Hint Resolve alpha_transitive : core.
  Local Hint Constructors Equivalence : core.

  Global Instance AlphaEquiv : Equivalence alpha.
  Proof. auto. Defined.
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
