Require Export CoqRecon.Unify.Unify.

Lemma tenv_compose_Ctsub : forall C s1 s2,
    Forall (uncurry (satisfy s1)) (Ctsub s2 C) <->
    Forall (uncurry (satisfy (s1 ‡ s2))) C.
Proof.
  intro C; induction C as [| [l r] C IHC];
    intros s1 s2; simpl; split;
      intros HC; inv HC; constructor; simpl in *;
        try (apply IHC; assumption);
        unfold satisfy in *;
        repeat rewrite tsub_assoc in *; try assumption.
Qed.

Hint Rewrite tenv_compose_Ctsub : core.

Theorem Unify_satisfies : forall C σ,
    Unify C σ ->
    Forall (uncurry (satisfy σ)) C.
Proof.
  intros C σ HU; induction HU; simpl in *;
    constructor; simpl; autorewrite with core in *;
      auto; try reflexivity.
  - unfold satisfy; subst s; simpl; unfold "‡"; simpl.
    rewrite bind_sound. rewrite bind_complete by lia; simpl.
    reflexivity.
  - unfold satisfy; subst s; simpl; unfold "‡"; simpl.
    rewrite bind_sound. rewrite bind_complete by lia; simpl.
    reflexivity.
  - unfold satisfy; subst s; simpl.
    rewrite tenv_compose_tsub_not_in_tvars
      with (t := τ) by assumption.
    rewrite tenv_compose_empty_l.
    unfold "‡". rewrite bind_sound. reflexivity.
  - unfold satisfy; subst s; simpl.
    rewrite tenv_compose_tsub_not_in_tvars
      with (t := τ) by assumption.
    rewrite tenv_compose_empty_l.
    unfold "‡". rewrite bind_sound. reflexivity.
  - inv IHHU. inv H3. simpl in *.
    unfold satisfy in *; simpl.
    f_equal; assumption.
  - inv IHHU. inv H3. assumption.
Qed.

Local Hint Constructors Unify : core.

Fixpoint flip_constraints (C : list (typ * typ)) : list (typ * typ) :=
  match C with
  | []         => []
  | (l, r) :: C => (r, l) :: flip_constraints C
  end.

Lemma flip_constraints_involutive : forall C,
    flip_constraints (flip_constraints C) = C.
Proof.
  intro C; induction C as [| [l r] C IHC]; simpl; f_equal; auto.
Qed.

Lemma flip_constraints_satisfies : forall C s,
    Forall (uncurry (satisfy s)) C <->
    Forall (uncurry (satisfy s)) (flip_constraints C).
Proof.
  intro C; induction C as [| [l r] C IHC];
    intros s; simpl; split; intros HC; inv HC;
      constructor; try rewrite IHC in *; auto;
        simpl in *; symmetry; assumption.
Qed.

Lemma Ctsub_flip_constraints_comm : forall C s,
    Ctsub s (flip_constraints C) = flip_constraints (Ctsub s C).
Proof.
  intro C; induction C as [| [l r] C IHC]; intro s; simpl; f_equal; auto.
Qed.

Lemma flip_constraints_nil : forall C,
    flip_constraints C = [] -> C = [].
Proof.
  intros C HC.
  destruct C as [| [? ?] ?];
    simpl in *; try discriminate; reflexivity.
Qed.

Lemma Unify_sym : forall C σ,
    Unify C σ <-> Unify (flip_constraints C) σ.
Proof.
  intros C s; split; intros HU.
  - induction HU; simpl; auto;
      try (rewrite <- Ctsub_flip_constraints_comm in IHHU;
           subst s; auto; assumption).
    intuition.
  - remember (flip_constraints C) as fcC eqn:Heqfc;
      generalize dependent C.
    induction HU; intros C' Heqfc.
    + symmetry in Heqfc.
      apply flip_constraints_nil in Heqfc; subst; auto.
    + destruct C' as [| [l' r'] C'];
        simpl in *; inv Heqfc; auto.
    + destruct C' as [| [l' r'] C'];
        simpl in *; inv Heqfc. subst s.
      apply Unify_cons_var_both_r; auto.
      apply IHHU. apply Ctsub_flip_constraints_comm.
    + destruct C' as [| [l' r'] C'];
        simpl in *; inv Heqfc. subst s.
      apply Unify_cons_var_both_l; auto.
      apply IHHU. apply Ctsub_flip_constraints_comm.
    + destruct C' as [| [l' r'] C'];
        simpl in *; inv Heqfc. subst s.
      constructor; auto.
      apply IHHU. apply Ctsub_flip_constraints_comm.
    + destruct C' as [| [l' r'] C'];
        simpl in *; inv Heqfc. subst s.
      constructor; auto.
      apply IHHU. apply Ctsub_flip_constraints_comm.
    + destruct C' as [| [l' r'] C']; inv Heqfc.
      intuition.
Qed.

Lemma unify_sym : forall C,
    unify (flip_constraints C) = unify C.
Proof.
  intro C.
  functional induction (unify C) using unify_ind;
    rewrite unify_equation; simpl; auto;
      try match goal with
          | H: typ_eq ?l ?r = _
            |- context [typ_eq ?r ?l]
            => rewrite typ_eq_sym, H
          end; auto.
  - assert (HRL: R <> L) by lia.
    rewrite <- Nat.eqb_neq in HRL.
    rewrite HRL.
    destruct (lt_eq_lt_dec R L) as [[? | ?] | ?]; try lia;
      maybe_simpl;
      try rewrite Ctsub_flip_constraints_comm, IHo; auto.
  - rewrite typ_eq_not_eq in e0. contradiction.
  - assert (HRL: R <> L) by lia.
    rewrite <- Nat.eqb_neq in HRL.
    rewrite HRL.
    destruct (lt_eq_lt_dec R L) as [[? | ?] | ?]; try lia;
      maybe_simpl;
      try rewrite Ctsub_flip_constraints_comm, IHo; auto.
  - destruct r; simpl in *;
      try discriminate; maybe_simpl.
    + rewrite e3; reflexivity.
    + repeat dispatch_eqdec; auto; try discriminate.
  - destruct r; simpl in *; maybe_simpl;
      try rewrite Ctsub_flip_constraints_comm;
      try rewrite IHo; try reflexivity.
    + rewrite e3; reflexivity.
    + repeat dispatch_eqdec; try discriminate.
  - destruct l; simpl in *;
      try discriminate; maybe_simpl.
    + rewrite e3; reflexivity.
    + repeat dispatch_eqdec; auto; try discriminate.
  - destruct l; simpl in *; maybe_simpl;
      try rewrite Ctsub_flip_constraints_comm;
      try rewrite IHo; try reflexivity.
    + rewrite e3; reflexivity.
    + repeat dispatch_eqdec; try discriminate.
  - simpl in *.
    rewrite typ_eq_sym with (l := r0).
    rewrite typ_eq_sym with (l := r').
    rewrite e0. assumption.
  - destruct l; destruct r; auto; try contradiction.
Qed.

Lemma unify_Unify : forall C σ,
    unify C = Some σ -> Unify C σ.
Proof.
  intros C.
  functional induction (unify C) using unify_ind;
    intros s Hu; try discriminate; auto.
  - inv Hu; auto.
  - rewrite typ_eq_iff in *; subst; auto.
  - maybe_simpl_hyp Hu.
    destruct (unify (Ctsub (L ↦ TVar R;; ∅) C0)) eqn:Hequ; inv Hu; auto.
  - maybe_simpl_hyp Hu.
    destruct (unify (Ctsub (R ↦ TVar L;; ∅) C0)) eqn:Hequ; inv Hu; auto.
  - rewrite Not_In_member_iff in e3.
    maybe_simpl_hyp Hu.
    destruct (unify (Ctsub (L ↦ r;; ∅) C0)) eqn:Hequ; inv Hu.
    apply Unify_cons_var_just_l; auto.
    intros Hr; inv Hr; contradiction.
  - rewrite Not_In_member_iff in e3.
    maybe_simpl_hyp Hu.
    destruct (unify (Ctsub (R ↦ l;; ∅) C0)) eqn:Hequ; inv Hu.
    apply Unify_cons_var_just_r; auto.
    intros Hl; inv Hl; contradiction.
  - simpl in *.
    rewrite andb_false_iff in e0.
    repeat rewrite typ_eq_not_eq in *. auto.
Qed.

Local Hint Constructors is_tvar : core.

Lemma Unify_unify : forall C σ,
    Unify C σ -> unify C = Some σ.
Proof.
  intros C s HU; induction HU;
    rewrite unify_equation; auto.
  - rewrite typ_eq_reflexive. assumption.
  - assert (HLR: TVar L <> TVar R).
    { intros HLR; inv HLR; try lia. }
    rewrite <- typ_eq_not_eq in HLR. rewrite HLR.
    destruct (lt_eq_lt_dec L R) as [[? | ?] | ?]; try lia.
    subst s; maybe_simpl. rewrite IHHU. reflexivity.
  - assert (HLR: TVar L <> TVar R).
    { intros HLR; inv HLR; try lia. }
    rewrite <- typ_eq_not_eq in HLR. rewrite HLR.
    destruct (lt_eq_lt_dec L R) as [[? | ?] | ?]; try lia.
    subst s; maybe_simpl. rewrite IHHU. reflexivity.
  - assert (HTτ: TVar T <> τ).
    { intros ?; subst; simpl in *; intuition. }
    rewrite <- typ_eq_not_eq in HTτ. rewrite HTτ.
    rewrite <- Not_In_member_iff in H0. rewrite H0.
    subst s. rewrite IHHU. maybe_simpl.
    destruct τ; intuition.
  - assert (HτT: τ <> TVar T).
    { intros ?; subst; simpl in *; intuition. }
    rewrite <- typ_eq_not_eq in HτT. rewrite HτT.
    rewrite <- Not_In_member_iff in H0. rewrite H0.
    subst s. rewrite IHHU. maybe_simpl.
    destruct τ; intuition.
  - pose proof typ_eq_reflects (t → τ) (t' → τ') as Hteq.
    inv Hteq; simpl.
    + inv H1. intuition.
    + rewrite <- H0. assumption.
Qed.

Local Hint Resolve Unify_unify : core.
Local Hint Resolve unify_Unify : core.

Theorem Unify_unify_iff : forall C σ,
    unify C = Some σ <-> Unify C σ.
Proof.
  intuition.
Qed.

Local Hint Resolve Unify_satisfies : core.

Theorem unify_satisfies : forall C σ,
    unify C = Some σ ->
    Forall (uncurry (satisfy σ)) C.
Proof.
  intuition.
Qed.
