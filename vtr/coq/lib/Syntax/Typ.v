Require Export Coq.Strings.String CoqRecon.Util.Env
        Coq.micromega.Lia Coq.Arith.PeanoNat.

Inductive typ : Set :=
| TBool
| TNat
| TArrow : typ -> typ -> typ
| TVar : nat -> typ.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Coercion TVar : nat >-> typ.
Notation "t1 → t2"
  := (TArrow t1 t2)
       (at level 30, right associativity) : typ_scope.

Open Scope typ_scope.

Fixpoint typ_eq (l r : typ) : bool :=
  match l, r with
  | TBool, TBool | TNat, TNat => true
  | TVar T1, TVar T2 => T1 =? T2
  | l → l', r → r'
    => typ_eq l r && typ_eq l' r'
  | _, _ => false
  end.

Fixpoint tvars (t : typ) : list nat :=
  match t with
  | TBool | TNat => []
  | TVar T => [T]
  | t → t' => tvars t ++ tvars t'
  end.

Fixpoint typ_size (t : typ) : nat :=
  match t with
  | TBool | TNat | TVar _ => 1
  | t → t' => 1 + typ_size t + typ_size t'
  end.

Definition typ_size_vars (t : typ) : nat * nat :=
  (length (uniques (tvars t)), typ_size t).

Definition Ctvars : list (typ * typ) -> list nat :=
  fold_right (fun '(l,r) acc => tvars l ++ tvars r ++ acc) [].

Definition C_size : list (typ * typ) -> nat :=
  fold_right (fun '(l,r) acc => typ_size l + typ_size r + acc) 0.

Definition C_size_vars (C : list (typ * typ)) : nat * nat :=
  (length (uniques (Ctvars C)), C_size C).
    
Section TypEq.
  Lemma typ_eq_reflexive : forall t, typ_eq t t = true.
  Proof.
    Local Hint Resolve andb_true_intro : core.
    Local Hint Resolve Nat.eqb_refl : core.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      simpl; try reflexivity; auto.
  Qed.
  
  Lemma typ_eq_eq : forall l r,
      typ_eq l r = true -> l = r.
  Proof.
    Hint Rewrite andb_true_iff : core.
    Hint Rewrite Nat.eqb_eq : core.
    intro l; induction l as [| | l IHl l' IHl' | L];
      intros [| | r r' | R] H; simpl in *;
        try discriminate; try reflexivity;
          autorewrite with core in *; f_equal; intuition.
  Qed.

  Local Hint Resolve typ_eq_reflexive : core.
  Local Hint Resolve typ_eq_eq : core.
  
  Lemma typ_eq_iff : forall l r,
      typ_eq l r = true <-> l = r.
  Proof.
    split; intros; subst; auto.
  Qed.

  Lemma typ_eq_reflects : reflects eq typ_eq.
  Proof.
    unfold reflects.
    intros l r; destruct (typ_eq l r) eqn:Hlr;
      constructor; intuition; subst.
    rewrite typ_eq_reflexive in Hlr.
    discriminate.
  Defined.

  Lemma typ_eq_not_eq : forall l r,
      typ_eq l r = false <-> l <> r.
  Proof.
    intros l r.
    pose proof typ_eq_reflects l r as Hlr; inv Hlr;
      intuition.
  Qed.

  Lemma typ_eq_sym : forall l r,
      typ_eq l r = typ_eq r l.
  Proof.
    intros l r.
    pose proof typ_eq_reflects l r as Hlr; inv Hlr; auto.
    apply not_eq_sym in H0.
    rewrite <- typ_eq_not_eq in H0.
    rewrite H0. reflexivity.
  Qed.
End TypEq.

Section TypSize.
  Lemma typ_size_non_zero : forall t,
    typ_size t > 0.
  Proof.
    intro t; induction t; simpl; lia.
  Qed.
End TypSize.

Definition tenv : Set := @env nat typ.

Reserved Notation "s † t" (at level 20, right associativity).

Fixpoint tsub (σ : tenv) (t : typ) {struct t} : typ :=
  match t with
  | TBool => TBool
  | TNat => TNat
  | t → t' => σ † t → σ † t'
  | TVar T => match σ T with
             | Some τ => τ
             | None => T
             end
  end
where "σ † t" := (tsub σ t) : typ_scope.

Definition Ctsub (s : tenv) : list (typ * typ) -> list (typ * typ) :=
  map (fun '(l,r) => (s † l, s † r)).

Definition tenv_compose (s1 s2 : tenv) : tenv :=
  fun T =>
    match s2 T with
    | Some t => Some (s1 † t)
    | None   => s1 T
    end.

Notation "s1 ‡ s2"
  := (tenv_compose s1 s2)
       (at level 21, left associativity) : env_scope.

Open Scope env_scope.

Definition satisfy σ τ1 τ2 : Prop := σ † τ1 = σ † τ2.

Section Satisfy.
  Lemma satisfy_reflexive : forall σ, Reflexive (satisfy σ).
  Proof.
    unfold Reflexive, satisfy; reflexivity.
  Qed.
  
  Lemma satisfy_symmetric : forall σ, Symmetric (satisfy σ).
  Proof.
    unfold Symmetric, satisfy; auto.
  Qed.
  
  Lemma satisfy_transitive : forall σ, Transitive (satisfy σ).
  Proof.
    unfold Transitive, satisfy; intros; etransitivity; eauto.
  Qed.
End Satisfy.

Definition gamma : Set := @env string typ.

Notation "s × g" := (env_map (tsub s) g)
                      (at level 25, right associativity) : env_scope.

Section TSub.
  Lemma tsub_empty : forall t, ∅ † t = t.
  Proof.
    intro t; induction t; simpl in *; auto.
    rewrite IHt1. rewrite IHt2. reflexivity.
  Qed.

  Open Scope set_scope.
  
  Lemma tsub_not_in_tvars : forall t t' T s,
      T ∉ tvars t ->
      (T ↦ t';; s) † t = s † t.
  Proof.
    intro t;
      induction t as [| | t1 IHt1 t2 IHt2 | X];
      intros t' T s HIn; simpl in *; auto.
    - rewrite in_app_iff in HIn.
      apply Decidable.not_or in HIn as [Ht1 Ht2].
      rewrite IHt1,IHt2 by eauto. reflexivity.
    - apply Decidable.not_or in HIn as [Ht _].
      rewrite bind_complete by intuition. reflexivity.
  Qed.

  Lemma tenv_compose_empty_l : forall s, s ‡ ∅ = s.
  Proof.
    intros s. extensionality T.
    unfold "‡"; reflexivity.
  Qed.

  Lemma tenv_compose_empty_r : forall s, ∅ ‡ s = s.
  Proof.
    intros s. extensionality T. unfold "‡".
    destruct (s T); try rewrite tsub_empty; reflexivity.
  Qed.

  Lemma tsub_assoc : forall t s1 s2,
      s1 † s2 † t = (s1 ‡ s2) † t.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros s1 s2; simpl; try reflexivity;
        try (f_equal; auto).
    unfold "‡". destruct (s2 T); simpl; reflexivity.
  Qed.
  
  Lemma tenv_compose_assoc : forall σ γ ϵ,
      σ ‡ (γ ‡ ϵ) = σ ‡ γ ‡ ϵ.
  Proof.
    intros s g e. extensionality T.
    unfold "‡".
    repeat match goal with
           | |- context [match ?a with
                        | Some _ => _
                        | None => _
                        end]
             => destruct a as [? |] eqn:?; simpl
           | H: Some _ = Some _ |- _ => inv H
           end; auto; try discriminate.
    f_equal. rewrite tsub_assoc. reflexivity.
  Qed.
  
  Lemma tenv_compose_tsub_not_in_tvars : forall t t' s1 s2 T,
      T ∉ tvars t ->
      (s1 ‡ T ↦ t';; s2) † t = (s1 ‡ s2) † t.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | X];
      intros t s1 s2 T HTt; simpl in *; try reflexivity.
    - rewrite in_app_iff in HTt.
      apply Decidable.not_or in HTt as [HTt1 HTt2].
      f_equal; auto.
    - unfold "‡". assert (X <> T) by intuition.
      rewrite bind_complete by assumption.
      reflexivity.
  Qed.
  
  Lemma Ctsub_empty : forall C,
      Ctsub ∅ C = C.
  Proof.
    intro C; induction C as [| [l r] C IHC]; simpl; auto.
    repeat rewrite tsub_empty. rewrite IHC. reflexivity.
  Qed.

  Lemma Ctsub_not_in_tvars : forall C T t s,
      T ∉ Ctvars C ->
      Ctsub (T ↦ t;; s) C = Ctsub s C.
  Proof.
    intro C; induction C as [| [l r] C IHC];
      intros T t s HT; simpl in *; auto.
    repeat rewrite in_app_iff in HT.
    apply Decidable.not_or in HT as [HT1 HT2].
    apply Decidable.not_or in HT2 as [HT2 HT3].
    repeat rewrite tsub_not_in_tvars by auto.
    rewrite IHC by auto. reflexivity.
  Qed.
  
  Lemma tsub_gamma_empty : forall g : gamma, (∅ × g = g).
  Proof.
    intros g. extensionality n.
    unfold env_map.
    destruct (g n) eqn:Heq; auto.
    rewrite tsub_empty. reflexivity.
  Qed.

  Lemma tsub_gamma_not_in_tvars : forall T t (g : gamma) (s : tenv),
      (forall x tx, g x = Some tx -> T ∉ tvars tx) ->
      ((T ↦ t;; s) × g = s × g).
  Proof.
    intros T t g s Hg.
    extensionality y.
    repeat rewrite env_map_map.
    maybe_simpl.
    destruct (g y) as [ty |] eqn:Hgy; auto.
    apply Hg in Hgy. f_equal.
    apply tsub_not_in_tvars; auto.
  Qed.
  
  Lemma tsub_length_count_tvars : forall τ t T,
      T ∉ tvars t ->
      length (tvars ((T ↦ t;; ∅) † τ)) =
      count T (tvars τ) * length (tvars t) +
      length (tvars τ) - count T (tvars τ).
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | X];
      intros t T HTt; simpl in *; auto.
    - apply IHt1 in HTt as IH1; clear IHt1;
        apply IHt2 in HTt as IH2; clear IHt2.
      repeat rewrite app_length. rewrite IH1, IH2.
      repeat rewrite count_app.
      pose proof count_length_le (tvars t1) T as HCL1.
      pose proof count_length_le (tvars t2) T as HCL2. lia.
    - unfold bind. dispatch_eqdec; try lia.
  Qed.

  Local Hint Resolve Permutation_refl : core.
  
  Lemma tsub_uniques_tvars_perm : forall τ t T,
      T ∉ tvars t -> T ∈ tvars τ ->
      Permutation
        (uniques (tvars ((T ↦ t;; ∅) † τ)))
        (uniques (remove T (tvars τ) ∪ tvars t)).
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | x];
      intros t T HTt HIn; simpl in *;
        try contradiction.
    - rewrite in_app_iff in HIn.
      pose proof In_member_reflects T (tvars t1) as HTt1.
      pose proof In_member_reflects T (tvars t2) as HTt2.
      inv HTt1; inv HTt2; rewrite remove_app.
      + pose proof IHt1 _ _ HTt H0 as IH1; clear IHt1.
        pose proof IHt2 _ _ HTt H2 as IH2; clear IHt2.
        rewrite <- app_assoc.
        apply uniques_uniques_perm_app; auto.
      + rewrite (remove_not_in (tvars t2)) by assumption.
        rewrite (tsub_not_in_tvars t2) by assumption.
        rewrite tsub_empty by assumption.
        apply perm_trans with
            (uniques (remove T (tvars t1) ∪ tvars t ∪ tvars t2)).
        * repeat rewrite (uniques_app _ (tvars t2)).
          apply uniques_perm. auto using Permutation_app.
        * apply uniques_perm. repeat rewrite <- app_assoc.
          apply Permutation_app_head. apply Permutation_app_swap.
      + rewrite (remove_not_in (tvars t1)) by assumption.
        rewrite (tsub_not_in_tvars t1) by assumption.
        rewrite tsub_empty by assumption.
        rewrite <- app_assoc.
        repeat rewrite (uniques_app (tvars t1)).
        apply uniques_perm. apply Permutation_app_head; auto.
      + intuition.
    - destruct HIn; subst; try contradiction.
      unfold bind. dispatch_eqdec; auto.
  Qed.

  Lemma Ctsub_perm_uniques_Ctvars : forall C t T,
      T ∉ tvars t -> T ∈ Ctvars C ->
      Permutation
        (uniques (Ctvars (Ctsub (T ↦ t ;; ∅) C)))
        (uniques (remove T (Ctvars C) ∪ tvars t)).
  Proof.
    intro C; induction C as [| [l r] C];
      intros t T HTt HTC; simpl in *; try contradiction.
    repeat rewrite in_app_iff in HTC.
    pose proof In_member_reflects T (tvars l) as HTl.
    pose proof In_member_reflects T (tvars r) as HTr.
    pose proof In_member_reflects T (Ctvars C) as HTC'.
    repeat rewrite remove_app.
    inv HTl; inv HTr; inv HTC';
      try (destruct HTC as [? | [? | ?]]; contradiction).
    - pose proof IHC _ _ HTt H4 as IH; clear IHC.
      pose proof tsub_uniques_tvars_perm _ _ _ HTt H0 as Hl.
      pose proof tsub_uniques_tvars_perm _ _ _ HTt H2 as Hr.
      pose proof uniques_uniques_perm_app3
           _ _ _ _ _ _ _ Hl Hr IH as Happ.
      repeat rewrite <- app_assoc in *. assumption.
    - pose proof tsub_uniques_tvars_perm _ _ _ HTt H0 as Hl.
      pose proof tsub_uniques_tvars_perm _ _ _ HTt H2 as Hr.
      rewrite (remove_not_in (Ctvars C)) by assumption.
      rewrite Ctsub_not_in_tvars by assumption.
      rewrite Ctsub_empty by assumption.
      pose proof uniques_uniques_perm_app _ _ _ Hl _ _ Hr as Happ.
      apply perm_trans with
          (uniques
             ((remove T (tvars l)
                      ++ remove T (tvars r)
                      ++ tvars t)
                ++ Ctvars C)).
      + repeat rewrite app_assoc in *.
        repeat rewrite (uniques_app _ (Ctvars C)).
        apply uniques_perm.
        apply Permutation_app_tail. assumption.
      + apply uniques_perm.
        repeat rewrite <- app_assoc.
        repeat apply Permutation_app_head.
        apply Permutation_app_swap.
    - pose proof IHC _ _ HTt H4 as IH; clear IHC.
      pose proof tsub_uniques_tvars_perm _ _ _ HTt H0 as Hl.
      rewrite (remove_not_in (tvars r)) by assumption.
      rewrite (tsub_not_in_tvars r) by assumption.
      rewrite tsub_empty.
      apply perm_trans with
          (uniques
             ((remove T (tvars l)
                      ++ remove T (Ctvars C)
                      ++ tvars t)
                ++ tvars r)).
      + apply perm_trans with
            (uniques
               ((tvars ((T ↦ t;; ∅) † l)
                       ++ Ctvars (Ctsub (T ↦ t;; ∅) C))
                  ++ tvars r)).
        * apply uniques_perm.
          repeat rewrite <- app_assoc.
          apply Permutation_app_head.
          apply Permutation_app_swap.
        * do 2 rewrite (uniques_app _ (tvars r)).
          apply uniques_perm.
          apply Permutation_app_tail.
          apply uniques_uniques_perm_app; assumption.
      + apply uniques_perm.
        repeat rewrite <- app_assoc.
        apply Permutation_app_head.
        rewrite (app_assoc (remove T (Ctvars C))).
        apply Permutation_app_swap.
    - pose proof tsub_uniques_tvars_perm _ _ _ HTt H0 as Hl.
      rewrite (remove_not_in (tvars r)) by assumption.
      rewrite (remove_not_in (Ctvars C)) by assumption.
      rewrite (tsub_not_in_tvars r) by assumption.
      rewrite (Ctsub_not_in_tvars C) by assumption.
      rewrite tsub_empty. rewrite Ctsub_empty.
      apply perm_trans with
          (uniques ((remove T (tvars l) ++ tvars t)
                      ++ tvars r ++ Ctvars C)).
      + rewrite (uniques_app (tvars ((T ↦ t;; ∅) † l))).
        rewrite (uniques_app (remove T (tvars l) ++ tvars t)).
        apply uniques_perm.
        apply Permutation_app_tail. assumption.
      + apply uniques_perm.
        repeat rewrite <- app_assoc.
        apply Permutation_app_head.
        apply Permutation_app_rot.
    - pose proof IHC _ _ HTt H4 as IH; clear IHC.
      pose proof tsub_uniques_tvars_perm _ _ _ HTt H2 as Hr.
      rewrite (remove_not_in (tvars l)) by assumption.
      rewrite (tsub_not_in_tvars l) by assumption.
      rewrite tsub_empty.
      repeat rewrite <- app_assoc.
      repeat rewrite (uniques_app (tvars l)).
      apply uniques_perm.
      apply Permutation_app_head.
      apply uniques_uniques_perm_app; assumption.
    - rewrite (remove_not_in (tvars l)) by assumption.
      rewrite (remove_not_in (Ctvars C)) by assumption.
      rewrite (tsub_not_in_tvars l) by assumption.
      rewrite (Ctsub_not_in_tvars) by assumption.
      rewrite tsub_empty. rewrite Ctsub_empty.
      repeat rewrite <- app_assoc.
      do 2 rewrite (uniques_app (tvars l)).
      apply uniques_perm.
      apply Permutation_app_head.
      apply perm_trans with
          (uniques ((remove T (tvars r) ++ tvars t) ++ Ctvars C)).
      + do 2 rewrite (uniques_app _ (Ctvars C)).
        apply uniques_perm. apply Permutation_app_tail.
        apply tsub_uniques_tvars_perm; assumption.
      + apply uniques_perm.
        repeat rewrite <- app_assoc.
        apply Permutation_app_head.
        apply Permutation_app_swap.
    - pose proof IHC _ _ HTt H4 as IH; clear IHC.
      rewrite (remove_not_in (tvars l)) by assumption.
      rewrite (remove_not_in (tvars r)) by assumption.
      repeat rewrite tsub_not_in_tvars by assumption.
      repeat rewrite tsub_empty.
      repeat rewrite <- app_assoc.
      do 2 rewrite (uniques_app (tvars l)).
      apply uniques_perm. apply Permutation_app_head.
      do 2 rewrite (uniques_app (tvars r)).
      apply uniques_perm. apply Permutation_app_head.
      assumption.
  Qed.
  
  Lemma tsub_length_uniques_tvars : forall τ t T,
      T ∉ tvars t -> T ∈ tvars τ ->
      length (uniques (tvars ((T ↦ t;; ∅) † τ))) =
      length (uniques (tvars τ ∪ tvars t)) - 1.
  Proof.
    intros τ t T HTt HTτ.
    pose proof tsub_uniques_tvars_perm _ _ _ HTt HTτ as H.
    apply Permutation_length in H.
    rewrite uniques_app in H.
    rewrite <- remove_uniques_comm in H.
    assert (HInu : T ∉ (uniques (tvars t))).
    { intros HTut.
      apply uniques_sound in HTut. contradiction. }
    pose proof remove_not_in _ _ HInu as Hru.
    rewrite <- Hru in H. rewrite <- remove_app in H.
    rewrite <- remove_uniques_comm in H.
    repeat rewrite <- uniques_app in H.
    rewrite count_remove_length in H.
    assert (T ∈ (tvars τ ∪ tvars t))
      by (rewrite in_app_iff; auto).
    rewrite count_uniques_in in H by assumption.
    assumption.
  Qed.

  Lemma Ctsub_length_uniques_Ctvars : forall C t T,
      T ∉ tvars t -> T ∈ Ctvars C ->
      length (uniques (Ctvars (Ctsub (T ↦ t ;; ∅) C))) =
      length (uniques (Ctvars C ∪ tvars t)) - 1.
  Proof.
    intros C t T HTt HTC.
    pose proof Ctsub_perm_uniques_Ctvars _ _ _ HTt HTC as HP.
    apply Permutation_length in HP. rewrite HP.
    rewrite <- (remove_not_in (tvars t) T) at 1 by assumption.
    rewrite <- remove_app. rewrite <- remove_uniques_comm.
    rewrite count_remove_length.
    assert (HTCt : T ∈ Ctvars C ∪ tvars t).
    { rewrite in_app_iff. intuition. }
    rewrite count_uniques_in by assumption. reflexivity.
  Qed.
End TSub.
