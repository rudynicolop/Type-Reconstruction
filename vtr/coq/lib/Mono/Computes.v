Require Export CoqRecon.Mono.Mono Coq.Arith.Compare_dec.

Open Scope maybe_scope.

Definition typs_of_op (o : op) : typ * typ :=
  match o with
  | And | Or  => (TBool, TBool)
  | Add | Sub => (TNat,  TNat)
  | Eq  | Lt  => (TNat,  TBool)
  end.

(** [cgen ing used g e = Some (τ, χ, C)]
    iff [cgen] is able to produce
    a type [τ] with constraints [C].
    [used] is the type names used thus far,
    whereas [ing] is the type names used in [g]. *)
Fixpoint cgen (ing used : list nat) (g : gamma) (e : term)
  : option (typ * list nat * list (typ * typ)) :=
  match e with
  | Bool _ => Some (TBool,[],[])
  | Nat _  => Some (TNat,[],[])
  | Var x  => let! t := g x in (t,[],[])
  | λ x ⇒ e =>
    let T := 1 + list_max (ing ∪ used) in
    let! (t,χ,C) := cgen (T :: ing) used (x ↦ TVar T;; g) e in
    (T → t, T :: χ, C)
  | e1 ⋅ e2 =>
    let* (t1,χ1,C1) := cgen ing used g e1 in
    let! (t2,χ2,C2) := cgen ing (used ∪ χ1) g e2 in
    let T := 1 + list_max (ing ∪ used ∪ χ1 ∪ χ2) in
    (TVar T, T :: χ1 ∪ χ2, (t1, t2 → T) :: C1 ∪ C2)
  | Cond e1 e2 e3 =>
    let* (t1,χ1,C1) := cgen ing used g e1 in
    let* (t2,χ2,C2) := cgen ing (used ∪ χ1) g e2 in
    let! (t3,χ3,C3) := cgen ing (used ∪ χ1 ∪ χ2) g e3 in
    (t2, χ1 ∪ χ2 ∪ χ3, (t1, TBool) :: (t2,t3) :: C1 ∪ C2 ∪ C3)
  | Op o e1 e2 =>
    let (t,t') := typs_of_op o in
    let* (t1,χ1,C1) := cgen ing used g e1 in
    let! (t2,χ2,C2) := cgen ing (used ∪ χ1) g e2 in
    (t', χ1 ∪ χ2, (t,t1) :: (t,t2) :: C1 ∪ C2)
  | LetIn x e1 e2 =>
    let* (t1,χ1,C1) := cgen ing used g e1 in
    let! (t2,χ2,C2) := cgen (tvars t1 ∪ ing) (used ∪ χ1) (x ↦ t1;; g) e2 in
    (t2, χ1 ∪ χ2, C1 ∪ C2)
  end.

Section CGEN.
  Local Hint Constructors op_typs : core.
  
  Lemma typs_of_op_sound : forall o t t',
      typs_of_op o = (t,t') -> op_typs o t t'.
  Proof.
    intros [] ? ? H; simpl in *;
      symmetry in H; inv H; auto.
  Qed.

  Local Hint Resolve typs_of_op_sound : core.

  Lemma typs_of_op_tvars_l : forall o t t',
      typs_of_op o = (t,t') -> tvars t = [].
  Proof.
    intros [] [] [] H; simpl in *;
      try discriminate; reflexivity.
  Qed.
  
  Lemma typs_of_op_tvars_r : forall o t t',
      typs_of_op o = (t,t') -> tvars t' = [].
  Proof.
    intros [] [] [] H; simpl in *;
      try discriminate; reflexivity.
  Qed.
  
  Local Hint Constructors constraint_typing : core.

  Ltac cgen_simpl :=
    match goal with
    | H: (match cgen ?u ?F ?g ?e with
          | Some _ => _
          | None => _
          end = Some (_,_,_))
      |- _
      => destruct (cgen u F g e)
        as [[[? ?] ?] |] eqn:?; simpl in *;
        try discriminate
    end.
  
  Ltac cgen_ind :=
    match goal with
    | |- forall e u used g t X C,
        cgen u used g e = Some (t,X,C) -> _
      => intro e;
      induction e as
        [ x
        | x e IHe
        | e1 IHe1 e2 IHe2
        | b | n
        | e1 IHe1 e2 IHe2 e3 IHe3
        | o e1 IHe1 e2 IHe2
        | x e1 IHe1 e2 IHe2 ]; intros u used g t X C Hgen;
      simpl in *; maybe_simpl_hyp Hgen;
      (* var *)
      [ destruct (g x) as [tg |] eqn:Hgxeq
      (* abs *)
      | cgen_simpl
      (* app *)
      | repeat cgen_simpl
      (* bool *)
      | idtac
      (* nat *)
      | idtac
      (* cond *)
      | repeat cgen_simpl
      (* op *)
      | destruct (typs_of_op o) as [to t'] eqn:Hop;
        simpl in *; repeat cgen_simpl
      (* let *)
      | repeat cgen_simpl ]; inv Hgen
    end.

  Ltac solve_dumb x Hg :=
    intros y ty Hgy Y HY;
    destruct (equiv_dec y x) as [Hxy | Hxy];
    unfold equiv, complement in *; simpl in *; subst;
    [ rewrite bind_sound in Hgy;
      inv Hgy; simpl in *; lia
    | rewrite bind_complete in Hgy by assumption;
      eapply Hg in Hgy; eauto; assumption ].

  Ltac solve_dumber Hg :=
    intros y ty Hgy Y HY; eapply Hg in Hgy; eauto; lia.

  Ltac solve_stupid :=
    unfold "⊆"; intros; repeat rewrite in_app_iff; eauto.

  Ltac solve_stupider :=
    unfold "⊆" in *; intros; simpl in *; intuition; assumption.
  
  Local Hint Resolve list_max_ge_in : core.

  Ltac max_destruct :=
    match goal with
    | H: context [ Init.Nat.max ?m ?n ] |- _
      => destruct (lt_eq_lt_dec m n) as [[? | ?] | ?];
        match goal with
        | H: m < n |- _ => rewrite (Nat.max_r m n) in * by lia
        | H: m = n |- _ => rewrite H in *; rewrite Nat.max_id in *
        | H: n < m |- _ => rewrite (Nat.max_l m n) in * by lia
        end; try lia
    end.

  Hint Rewrite list_max_app : core.

  Lemma list_max_cons : forall n l,
      list_max (n :: l) = Nat.max n (list_max l).
  Proof.
    intros n l.
    replace (n :: l) with ([n] ++ l) by reflexivity.
    autorewrite with core; simpl; lia.
  Qed.
  
  Lemma cgen_used_X : forall e ing used g t X C,
      cgen ing used g e = Some (t,X,C) ->
      forall T, T ∈ X -> list_max (ing ∪ used) < T.
  Proof.
    intro e; intros.
    rewrite list_max_app. revert_until e.
    revert e.
    cgen_ind; intros T HX; simpl in *;
      autorewrite with core in *; try lia.
    - destruct HX as [HX | HX];
        repeat max_destruct;
        eapply IHe with (T := T) in Heqo; eauto;
          rewrite list_max_cons in *; max_destruct.
    - rewrite in_app_iff in *.
      destruct HX as [HX | [HX | HX]];
        repeat max_destruct;
        subst; try lia; eauto.
      eapply IHe2 in Heqo0; eauto.
      autorewrite with core in *.
      max_destruct; try lia.
    - repeat rewrite in_app_iff in HX.
      destruct HX as [[HX | HX] | HX].
      + eapply IHe1 in Heqo; eauto.
      + eapply IHe2 in Heqo0; eauto.
        rewrite list_max_app in Heqo0; lia.
      + eapply IHe3 in Heqo1; eauto.
        autorewrite with core in *. lia.
    - rewrite in_app_iff in HX.
      destruct HX as [HX | HX]; subst; try lia.
      + eapply IHe1 in Heqo0; eauto.
      + eapply IHe2 in Heqo1; eauto.
        autorewrite with core in *; lia.
    - rewrite in_app_iff in HX.
      destruct HX as [HX | HX]; eauto.
      eapply IHe2 in Heqo0; eauto.
      apply list_max_ge_in in HX as HX'.
      autorewrite with core in *.
      repeat max_destruct.
  Qed.

  Ltac populate_cgen_used_X :=
    match goal with
    | He: cgen _ _ _ _ = Some (_,?X,_), HT: _ ∈ ?X
      |- _ => pose proof _ _ _ _ _ _ _ He _ HT as ?
    end.
  
  Local Hint Resolve cgen_used_X : core.
  
  Corollary cgen_used : forall e ing used g t X C,
      cgen ing used g e = Some (t,X,C) ->
      forall T, T ∈ (ing ∪ used) -> T ∉ X.
  Proof.
    intros e u used g t X C Hgen T Hused HX.
    pose proof cgen_used_X _ _ _ _ _ _ _ Hgen _ HX as H.
    rewrite in_app_iff in Hused.
    rewrite list_max_app in H.
    apply list_max_ge_in in HX as HXT.
    destruct Hused as [HT | HT];
      apply list_max_ge_in in HT as HT'; max_destruct; try lia.
  Qed.

  Ltac populate_cgen_used :=
    match goal with
    | He: cgen_used ?ing ?used _ _ = Some _, HT: ?T ∈ ?ing
      |- _ => eapply cgen_used with (T := T) in He; eauto
    | He: cgen_used ?ing ?used _ _ = Some _, HT: ?T ∈ ?used
      |- _ => eapply cgen_used with (T := T) in He; eauto
    | He: cgen_used ?ing ?used _ _ = Some _, HT: _ ∈ ?used ∪ ?ing
      |- _ => pose proof cgen_used _ _ _ _ _ _ _ He _ HT as ?
    end.
  
  Local Hint Resolve cgen_used : core.
  
  Lemma cgen_tvars : forall e ing used g t X C,
      cgen ing used g e = Some (t,X,C) ->
      (forall x t, g x = Some t -> tvars t ⊆ ing) ->
      tvars t ⊆ ing ∪ X.
  Proof.
    unfold "⊆".
    cgen_ind; intros Hg T HT; simpl in *;
      repeat rewrite in_app_iff in *;
      simpl in *; try lia; eauto.
    - destruct HT as [HT | HT]; subst; auto.
      eapply IHe in Heqo; eauto;
        try solve_dumb x Hg; try solve_stupider.
      simpl in Heqo. rewrite in_app_iff in Heqo.
      intuition.
    - eapply IHe2 in Heqo0; eauto; try solve_stupid.
      repeat rewrite in_app_iff in Heqo0.
      intuition.
    - erewrite typs_of_op_tvars_r in HT; eauto.
      simpl in HT; contradiction.
    - eapply IHe2 in Heqo0; eauto.
      + repeat rewrite in_app_iff in *. intuition.
        eapply IHe1 in Heqo; eauto.
        rewrite in_app_iff in *. intuition.
      + intros y t' Hyt' Y HY. unfold bind in *.
        dispatch_eqdec.
        * inv Hyt'. intuition.
        * eapply Hg in Hyt'; eauto. intuition.
  Qed.

  Ltac populate_cgen_tvars e H :=
    match goal with
    | He: cgen _ _ _ e = Some _
      |- _ => apply cgen_tvars in He as H; eauto; try solve_stupid
    end.
  
  Local Hint Resolve cgen_tvars : core.

  Lemma In_Ctvars_app : forall C1 C2 X,
      X ∈ Ctvars (C1 ∪ C2) <-> X ∈ Ctvars C1 \/ X ∈ Ctvars C2.
  Proof.
    intro C1; induction C1 as [| [l1 r2] C1 IHC1];
      intros C2 X; simpl in *; intuition;
        repeat rewrite in_app_iff in *;
        rewrite IHC1 in *; intuition.
  Qed.
  
  Lemma cgen_Ctvars : forall e ing used g t X C,
      cgen ing used g e = Some (t,X,C) ->
      (forall x t, g x = Some t -> tvars t ⊆ ing) ->
      Ctvars C ⊆ ing ∪ X.
  Proof.
    unfold "⊆".
    cgen_ind; intros Hg T HT; simpl in *;
      repeat rewrite in_app_iff in *;
      simpl in *; try lia; eauto.
    - eapply IHe in Heqo; eauto;
        try solve_dumb x Hg; try solve_stupider.
      rewrite in_app_iff in Heqo; simpl in *.
      intuition.
    - rewrite In_Ctvars_app in HT.
      rewrite in_app_iff. intuition.
      + eapply cgen_tvars in Heqo; unfold "⊆" in *; eauto.
        apply Heqo in H.
        rewrite in_app_iff in H. intuition.
      + eapply cgen_tvars in Heqo0; eauto; unfold "⊆" in *;
          try solve_stupid.
        apply Heqo0 in H.
        repeat rewrite in_app_iff in H. intuition.
      + eapply IHe1 in Heqo; eauto.
        rewrite in_app_iff in Heqo. intuition.
      + eapply IHe2 in Heqo0; eauto; try solve_stupid.
        repeat rewrite in_app_iff in Heqo0.
        intuition.
    - repeat rewrite In_Ctvars_app in HT.
      intuition.
      + eapply cgen_tvars in Heqo; eauto.
        unfold "⊆" in *. apply Heqo in H.
        rewrite in_app_iff in H.
        intuition.
      + eapply cgen_tvars in Heqo0; eauto; unfold "⊆" in *;
          try solve_stupid.
        apply Heqo0 in H0.
        repeat rewrite in_app_iff in H0.
        intuition.
      + eapply cgen_tvars in Heqo1; eauto; unfold "⊆" in *;
          try solve_stupid.
        apply Heqo1 in H.
        repeat rewrite in_app_iff in H.
        intuition.
      + eapply IHe1 in Heqo; eauto.
        rewrite in_app_iff in Heqo.
        intuition.
      + eapply IHe2 in Heqo0; eauto; try solve_stupid.
        repeat rewrite in_app_iff in Heqo0.
        intuition.
      + eapply IHe3 in Heqo1; eauto; try solve_stupid.
        repeat rewrite in_app_iff in Heqo1.
        intuition.
    - rewrite In_Ctvars_app in HT.
      apply typs_of_op_tvars_l in Hop.
      repeat rewrite Hop in HT; simpl in *.
      intuition.
      + eapply cgen_tvars in Heqo0; eauto.
        apply Heqo0 in H0.
        rewrite in_app_iff in H0.
        intuition.
      + eapply cgen_tvars in Heqo1; eauto; try solve_stupid.
        apply Heqo1 in H0.
        repeat rewrite in_app_iff in H0.
        intuition.
      + eapply IHe1 in Heqo0; eauto.
        rewrite in_app_iff in Heqo0.
        intuition.
      + eapply IHe2 in Heqo1; eauto; try solve_stupid.
        repeat rewrite in_app_iff in Heqo1.
        intuition.
    - rewrite In_Ctvars_app in HT.
      destruct HT as [HT | HT].
      + eapply IHe1 in Heqo as HC1; eauto.
        rewrite in_app_iff in *. intuition.
      + eapply IHe2 in Heqo0 as HC2; eauto.
        repeat rewrite in_app_iff in *. intuition.
        * eapply cgen_tvars in Heqo as Ht1; eauto.
          apply Ht1 in H0. rewrite in_app_iff in *.
          intuition.
        * intros y t' Hyt' Y HY.
          unfold bind in Hyt'.
          dispatch_eqdec.
          -- inv Hyt'. intuition.
          -- eapply Hg in Hyt'; eauto. intuition.
  Qed.

  Ltac populate_cgen_Ctvars e H :=
    match goal with
    | He: cgen _ _ _ e = Some _
      |- _ => apply cgen_Ctvars in He as H; eauto; try solve_stupid
    end.
  
  Local Hint Resolve cgen_Ctvars : core.
  Local Hint Resolve Subset_l_union : core.
  Local Hint Resolve Subset_r_union : core.

  Ltac populate_list_max_ge_in :=
    match goal with
    | H: _ ∈ _ |- _ => apply list_max_ge_in in H
    end.

  Ltac apply_subset :=
    match goal with
    | H: ?a ⊆ ?b, Ha: _ ∈ ?a |- _ => apply H in Ha
    end.
  
  Theorem cgen_sound : forall e ing used g t X C,
      cgen ing used g e = Some (t,X,C) ->
      (forall x t, g x = Some t -> tvars t ⊆ ing) ->
      g ⊢ e ∴ t ⊣ X ≀ C.
  Proof.
    cgen_ind; intros Hg; eauto.
    - constructor; eauto.
      + eapply cgen_used in Heqo; eauto; intuition.
      + eapply IHe in Heqo; eauto;
          try solve_stupider; try solve_dumb x Hg.
    - constructor; eauto.
      + apply Inter_nil; unfold Intersection.
        simpl; intro T; split; try contradiction.
        intros [HT1 HT2].
        assert (T ∈ used ∪ l) by intuition.
        eapply cgen_used in Heqo0 as He2; eauto; intuition.
      + apply Inter_nil; unfold Intersection.
        simpl; intro T; split; try contradiction.
        intros [HT1 HT2].
        eapply cgen_used_X in Heqo as He1; eauto.
        assert (T ∈ ing ∪ (used ∪ l)) by intuition.
        eapply cgen_used with (T := T) in Heqo0 as He2; eauto.
        eapply cgen_tvars in Heqo0 as He2'; eauto.
        apply He2' in HT2. rewrite in_app_iff in HT2.
        intuition. rewrite list_max_app in He1.
        apply list_max_ge_in in H0.
        max_destruct; try lia.
      + apply Inter_nil; unfold Intersection.
        simpl; intro T; split; try contradiction.
        intros [HT1 HT2].
        eapply cgen_tvars in Heqo as He1; eauto.
        eapply cgen_used_X in Heqo0 as He2; eauto.
        apply Subset_list_max in He1 as He1'.
        apply list_max_ge_in in HT2 as HT2'.
        apply He1 in HT2 as HT2''.
        rewrite in_app_iff in HT2''.
        repeat rewrite list_max_app in *.
        destruct HT2'' as [HT2'' | HT2''];
          apply list_max_ge_in in HT2'' as HT2''';
          repeat max_destruct; try lia.
      + populate_cgen_tvars e1 Ht1; apply Subset_list_max in Ht1 as Ht1'.
        populate_cgen_tvars e2 Ht2; apply Subset_list_max in Ht2 as Ht2'.
        populate_cgen_Ctvars e1 HC1; apply Subset_list_max in HC1 as HC1'.
        populate_cgen_Ctvars e2 HC2; apply Subset_list_max in HC2 as HC2'.
        repeat rewrite in_app_iff.
        repeat rewrite list_max_app in *.
        intuition;
          max_destruct;
          populate_list_max_ge_in;
          repeat apply_subset; max_destruct.
    - constructor; eauto;
        apply Inter_nil; unfold Intersection;
          simpl; intro T; split; try contradiction;
            intros [HT1 Ht2].
      + eapply cgen_used_X in Heqo as H1; eauto.
        eapply cgen_used_X in Heqo0 as H2; eauto.
        eapply cgen_used in Heqo0 as H2'; eauto; intuition.
      + eapply cgen_used_X in Heqo as H1; eauto.
        eapply cgen_used_X in Heqo1 as H2; eauto.
        eapply cgen_used in Heqo1 as H2'; eauto.
        repeat rewrite in_app_iff. intuition.
      + eapply cgen_used_X in Heqo0 as H1; eauto.
        eapply cgen_used_X in Heqo1 as H2; eauto.
        eapply cgen_used in Heqo1 as H2'; eauto. intuition.
    - constructor; eauto.
      apply Inter_nil; unfold Intersection;
          simpl; intro T; split; try contradiction;
            intros [HT1 Ht2].
      eapply cgen_used_X in Heqo0 as H1; eauto.
      eapply cgen_used_X in Heqo1 as H2; eauto.
      eapply cgen_used in Heqo1 as H2'; eauto; intuition.
    - econstructor; eauto.
      + apply Inter_nil; unfold Intersection;
          simpl; intro T; split; try contradiction;
            intros [HT1 HT2].
        eapply cgen_used_X in Heqo as H1; eauto.
        eapply cgen_used_X in Heqo0 as H2; eauto.
        eapply cgen_used in Heqo0 as H2'; eauto; intuition.
      + eapply IHe2; eauto.
        intros y ty Hyty Y HY.
        unfold bind in Hyty.
        dispatch_eqdec.
        * inv Hyty. intuition.
        * eapply Hg in Hyty; eauto.
          intuition.
  Qed.

  Theorem cgen_sound_clean : forall e t X C,
      cgen [] [] ∅ e = Some (t,X,C) ->
      ∅ ⊢ e ∴ t ⊣ X ≀ C.
  Proof.
    intros e t X C H.
    eapply cgen_sound; eauto.
    unfold "∅"; intros; discriminate.
  Qed.

  Lemma typs_of_op_complete : forall o t t',
      op_typs o t t' -> typs_of_op o = (t,t').
  Proof.
    intros o t t' H; inv H; simpl; reflexivity.
  Qed.
  
  Local Hint Resolve typs_of_op_complete : core.
  Local Hint Resolve tsub_gamma_empty : core.
  Local Hint Resolve tsub_empty : core.
  
  Lemma cgen_complete : forall Γ e τ X C,
      Γ ⊢ e ∴ τ ⊣ X ≀ C ->
      forall g σ,
        (σ × g = Γ)%env ->
        forall used,
          (forall x tx, g x = Some tx -> (tvars tx) ⊆ used)%set ->
          exists t X' C',
            (σ † t = τ)%typ /\
            Ctsub σ C' = C /\
            cgen [] used g e = Some (t,X',C').
  Proof. (*
    intros Γ e τ X C H;
      induction H;
      intros g s Hsg used Hused; simpl; maybe_simpl.
    - exists TBool. exists []. exists [].
      repeat split; simpl; auto.
    - exists TNat. exists []. exists [].
      repeat split; simpl; auto.
    - unfold bound in H.
      assert
        (Ht': exists t', g x = Some t' /\ (s † t' = τ)%typ).
      { rewrite <- Hsg in H.
        rewrite env_map_map in H.
        maybe_simpl_hyp H.
        destruct (g x) as [tx |] eqn:gx;
          simpl in *; inv H. eauto. }
      destruct Ht' as [t' [Ht' Hst']].
      exists t'. exists []. exists []. rewrite Ht'.
      repeat split; auto.
    - pose proof IHconstraint_typing
           (x ↦ TVar (S (list_max used));; g)%env
           ((S (list_max used)) ↦ TVar T;; s)%env as IH;
        clear IHconstraint_typing.
      assert
        (Heq:
           (S (list_max used) ↦ TVar T;;
            s × x ↦ TVar (S (list_max used));; g)%env =
           (x ↦ TVar T;; Γ)%env).
      { rewrite <- env_map_bind; simpl.
        rewrite bind_sound.
        rewrite tsub_gamma_not_in_tvars.
        - rewrite Hsg; reflexivity.
        - intros y ty Hgy HIn.
          apply Hused in Hgy.
          apply Hgy in HIn.
          apply list_max_ge_in in HIn. lia. }
      pose proof IH Heq as IH'; clear IH;
        rename IH' into IH.
      specialize IH with (S (list_max used) :: used).
      assert (Hy: forall y ty,
                 (x ↦ TVar (S (list_max used));; g)%env y = Some ty ->
                 (tvars ty ⊆ S (list_max used) :: used)%set)
        by solve_dumb x Hused.
      pose proof IH Hy as
          (t' & X' & C' & Ht' & HC' & Hgen); clear IH Hy.
      rewrite Hgen.
      exists (TVar (S (list_max used)) → t')%typ.
      exists (S (list_max used) :: X'). exists C'.
      repeat split; auto.
      + simpl. admit. (* Sudoku paradox. *)
      + admit. (* Sudoku paradox. *)
    - (* This is masochistic... *) *)
  Abort.
End CGEN.
