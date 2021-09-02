Require Export Coq.Bool.Bool CoqRecon.Util.ListLib.

Declare Scope set_scope.
Delimit Scope set_scope with set.

Reserved Notation "l ∪ r" (at level 45, left associativity).
Reserved Notation "l ∩ r" (at level 44, left associativity).
Reserved Notation "l ∖ r" (at level 43, left associativity).

Notation "e ∈ s"
  := (In e s)
       (at level 80, no associativity) : set_scope.

Notation "e ∉ s"
  := (~ In e s)
       (at level 80, no associativity) : set_scope.

(** [l ⊆ r] *)
Definition Subset {A : Set} (l r : list A) : Prop :=
  forall a, (a ∈ l -> a ∈ r)%set.

Notation "l ⊆ r"
  := (Subset l r)
       (at level 80, no associativity) : set_scope.

Definition set_equiv {A : Set} (l r : list A) : Prop :=
  (l ⊆ r /\ r ⊆ l)%set.

Notation "l ≡ r"
  := (set_equiv l r)
       (at level 80, no associativity) : set_scope.

Section SetEquiv.
  Open Scope set_scope.

  Context {A : Set}.

  Local Hint Unfold set_equiv : core.
  Local Hint Unfold Subset : core.
  Local Hint Unfold Reflexive : core.
  
  Lemma set_equiv_Reflexive :
    Reflexive (@set_equiv A).
  Proof.
    autounfold with core; auto.
  Qed.

  Local Hint Unfold Symmetric : core.
  
  Lemma set_equiv_Symmetric :
    Symmetric (@set_equiv A).
  Proof.
    autounfold with core; intuition.
  Qed.

  Local Hint Unfold Transitive : core.

  Lemma set_equiv_Transitive :
    Transitive (@set_equiv A).
  Proof.
    autounfold with core; intuition.
  Qed.
End SetEquiv.
  
Section SetDefs.
  Context {A : Set}.

  Open Scope set_scope.
  
  Local Hint Unfold Subset : core.
  Local Hint Resolve Permutation_in : core.
  Local Hint Resolve Permutation_sym : core.

  Lemma Subset_perm_l : forall l l' : list A,
      Permutation l l' ->
      forall r, l ⊆ r -> l' ⊆ r.
  Proof. eauto. Qed.

  Lemma Subset_perm_r : forall r r' : list A,
      Permutation r r' ->
      forall l, l ⊆ r -> l ⊆ r'.
  Proof. eauto. Qed.
  
  (** [u] is the union of [l] & [r]. *)
  Definition Union (l r u : list A) : Prop :=
    forall a, a ∈ u <-> a ∈ l \/ a ∈ r.

  Local Hint Unfold Union : core.

  Lemma Union_Subset_l : forall l r u,
      Union l r u -> l ⊆ u.
  Proof. firstorder. Qed.

  Lemma Union_Subset_r : forall l r u,
      Union l r u -> r ⊆ u.
  Proof. firstorder. Qed.

  Lemma Union_perm_l : forall l l',
      Permutation l l' ->
      forall r u, Union l r u -> Union l' r u.
  Proof. firstorder eauto. Qed.

  Lemma Union_perm_r : forall r r',
      Permutation r r' ->
      forall l u, Union l r u -> Union l r' u.
  Proof. firstorder eauto. Qed.

  Lemma Union_perm_u : forall u u',
      Permutation u u' ->
      forall l r, Union l r u -> Union l r u'.
  Proof. firstorder eauto. Qed.
      
  (** [i] is the intersection of [l] & [r]. *)
  Definition Intersection (l r i : list A) : Prop :=
    forall a, a ∈ i <-> a ∈ l /\ a ∈ r.

  Definition Disjoint (l r : list A) : Prop := Intersection l r [].

  Local Hint Unfold Intersection : core.

  Lemma Inter_Subset_l : forall l r i,
      Intersection l r i -> i ⊆ l.
  Proof.
    firstorder.
  Qed.

  Lemma Inter_Subset_r : forall l r i,
      Intersection l r i -> i ⊆ r.
  Proof.
    firstorder.
  Qed.

  Lemma Inter_perm_l : forall l l',
      Permutation l l' ->
      forall r i, Intersection l r i -> Intersection l' r i.
  Proof. firstorder eauto. Qed.

  Lemma Inter_perm_r : forall r r',
      Permutation r r' ->
      forall l i, Intersection l r i -> Intersection l r' i.
  Proof. firstorder eauto. Qed.

  Lemma Intersection_perm_i : forall i i',
      Permutation i i' ->
      forall l r, Intersection l r i -> Intersection l r i'.
  Proof.
    autounfold with core.
    intros i i' HP l r H a;
      pose proof H a as [Hai  Halr];
      split; eauto.
  Qed.
  
  (** [d] is the diff of [l] & [r]. *)
  Definition Difference (l r d : list A) : Prop :=
    forall a, a ∈ d <-> a ∈ l /\ a ∉ r.

  Local Hint Unfold Difference : core.
  
  Lemma Diff_Subset : forall l r d,
      Difference l r d -> d ⊆ l.
  Proof.
    firstorder.
  Qed.

  Lemma Diff_perm_l : forall l l',
      Permutation l l' ->
      forall r d, Difference l r d -> Difference l' r d.
  Proof. firstorder eauto. Qed.

  Lemma Diff_perm_r : forall r r',
      Permutation r r' ->
      forall l d, Difference l r d -> Difference l r' d.
  Proof. firstorder eauto. Qed.

  Lemma Diff_perm_u : forall d d',
      Permutation d d' ->
      forall l r, Difference l r d -> Difference l r d'.
  Proof.
    autounfold with core.
    intros d d' HP l r HD a;
      pose proof HD a as [Had Halr]; split; eauto.
  Qed.

  Lemma Subset_Diff : forall l r,
      l ⊆ r ->
      Difference l r [].
  Proof.
    unfold Subset, Difference.
    intros l r Hs a; simpl; intuition.
  Qed.

  Lemma Subset_cons : forall l r : list A,
      l ⊆ r -> forall a : A, a :: l ⊆ a :: r.
  Proof.
    unfold Subset; intros;
      simpl in *; intuition.
  Qed.
End SetDefs.

Section ComputeSets.
  Context {A : Set} {HEA: EqDec A eq}.
  
  Fixpoint member (a : A) (l : list A) : bool :=
    match l with
    | []    => false
    | h :: t => if a == h then true else member a t
    end.
  
  Fixpoint intersect (l r : list A) : list A :=
    match l with
    | []    => []
    | h :: t =>
      (if member h r then [h] else []) ++ intersect t r
    end.

  Fixpoint difference (l r : list A) : list A :=
    match l with
    | []    => []
    | h :: t =>
      (if member h r then [] else [h]) ++ difference t r
    end.
End ComputeSets.

Notation "l ∪ r" := (l ++ r) : set_scope.
Notation "l ∩ r" := (intersect l r) : set_scope.
Notation "l ∖ r" := (difference l r) : set_scope.

Section Sets.
  Open Scope set_scope.
  
  Context {A : Set} {HEA: EqDec A eq}.

  Local Hint Unfold Subset : core.
  Local Hint Unfold Union : core.
  Local Hint Unfold Intersection : core.
  Local Hint Unfold Difference : core.
  
  Lemma append_Union : forall l r : list A, Union l r (l ∪ r).
  Proof.
    auto using in_app_iff.
  Qed.

  Lemma In_member : forall a l, a ∈ l -> member a l = true.
  Proof.
    intros a l; induction l as [| h t IHt];
      intro H; simpl in *;
        [ contradiction | destruct H as [H | H]]; subst;
          dispatch_eqdec; auto.
  Qed.

  Local Hint Resolve In_member : core.
  
  Lemma member_In : forall a l, member a l = true -> a ∈ l.
  Proof.
    intros a l; induction l as [| h t IHt];
      intro H; simpl in *; try discriminate;
        dispatch_eqdec; auto.
  Qed.

  Local Hint Resolve member_In : core.

  Lemma In_member_iff : forall a l,
      member a l = true <-> In a l.
  Proof.
    intuition.
  Qed.
  
  Lemma In_member_reflects : reflects (@In A) member.
  Proof.
    Local Hint Constructors reflect : core.
    unfold reflects.
    intros a l; destruct (member a l) eqn:Hmem; auto.
    constructor. intros H. apply In_member in H.
    rewrite H in Hmem. discriminate.
  Qed.

  Lemma Not_In_member_iff : forall a l,
      member a l = false <-> a ∉ l.
  Proof.
    intros a l.
    pose proof In_member_reflects a l as H.
    inv H; intuition.
  Qed.

  Lemma member_app_or : forall a l r,
      member a (l ∪ r) = member a l || member a r.
  Proof.
    intros a l r.
    pose proof In_member_reflects a l as Hal; inv Hal; simpl.
    - assert (HIn : In a (l ++ r)).
      { rewrite in_app_iff; auto. }
      auto using In_member.
    - pose proof In_member_reflects a r as Har; inv Har.
      + assert (HIn : In a (l ++ r)).
        { rewrite in_app_iff; auto. }
        auto using In_member.
      + rewrite Not_In_member_iff.
        rewrite in_app_iff. intuition.
  Qed.

  Lemma member_repeat : forall n a,
      member a (repeat a n) =
      match n with
      | O => false
      | S _ => true
      end.
  Proof.
    intros [| n] a; simpl; auto. dispatch_eqdec; auto.
  Qed.

  Lemma intersect_Intersection : forall l r,
      Intersection l r (l ∩ r).
  Proof.
    unfold Intersection; intro l;
      induction l as [| h t IHt];
      intros r a; simpl in *.
    - intuition.
    - split.
      + pose proof (In_member_reflects h r) as H; inv H; simpl.
        * intros [H | H]; subst; firstorder.
        * firstorder.
      + intros [[Hha | Hat] Har]; subst.
        * rewrite In_member by auto; simpl; auto.
        * rewrite in_app_iff. firstorder.
  Qed.

  Lemma difference_Difference : forall l r,
      Difference l r (l ∖ r).
  Proof.
    unfold Difference; intro l;
      induction l as [| h t IHt];
      intros r a; simpl in *.
    - intuition.
    - split.
      + pose proof In_member_reflects h r as H; inv H; simpl.
        * intros H; apply IHt in H as [IH IHr]. intuition.
        * intros [H | H]; subst; intuition;
            apply IHt in H; intuition.
      + intros [[Hha | Hat] Har]; subst.
        * assert (member a r = false).
          { pose proof In_member_reflects a r as H; inv H;
              auto; contradiction. }
          rewrite H. rewrite in_app_iff. intuition.
        * rewrite in_app_iff. right.
          apply IHt. intuition.
  Qed.

  Lemma diff_empty_r : forall l : list A,
      l ∖ [] = l.
  Proof.
    intro l; induction l as [| h l]; simpl; auto.
    rewrite IHl. reflexivity.
  Qed.

  Lemma remove_diff_cons : forall l r a,
      l ∖ (a :: r) = remove a (l ∖ r).
  Proof.
    intro l; induction l as [| h l IHl];
      intros r a; simpl; auto.
    destruct (member h r) eqn:Hmemhr;
      repeat dispatch_eqdec; try rewrite IHl; reflexivity.
  Qed.
  
  Lemma remove_diff : forall l r : list A,
      fold_right remove l r = l ∖ r.
  Proof.
    intro l; induction l as [| a l IHl];
      intro r; induction r as [| x r IHr]; simpl in *; auto.
    - rewrite IHr. reflexivity.
    - f_equal. rewrite diff_empty_r. reflexivity.
    - dispatch_eqdec.
      + rewrite IHr. rewrite remove_app.
        destruct (member x r); simpl.
        * rewrite remove_diff_cons. reflexivity.
        * dispatch_eqdec.
          rewrite remove_diff_cons. reflexivity.
      + destruct (member a r) eqn:Hmemar; simpl in *.
        * rewrite IHr. rewrite remove_diff_cons. reflexivity.
        * rewrite IHr; simpl.
          dispatch_eqdec; f_equal.
          rewrite remove_diff_cons. reflexivity.
  Qed.

  Lemma Subset_difference : forall l r,
      l ⊆ r -> l ∖ r = [].
  Proof.
    intros l r Hlr. apply Subset_Diff in Hlr.
    unfold Difference in Hlr.
    induction l as [| h l IHl]; simpl; auto.
    pose proof In_member_reflects h r as Hhr; inv Hhr; simpl; firstorder.
  Qed.

  Corollary difference_same : forall l : list A,
      l ∖ l = [].
  Proof.
    intros l. apply Subset_difference.
    intuition.
  Qed.

  Corollary uniques_app_diff : forall l r: list A,
      uniques (l ++ r) = uniques l ++ difference (uniques r) l.
  Proof.
    intros l r. rewrite uniques_app2.
    f_equal. rewrite remove_diff. reflexivity.
  Qed.

  Corollary uniques_app_same : forall l : list A,
      uniques (l ++ l) = uniques l.
  Proof.
    intros l. rewrite uniques_app_diff.
    rewrite Subset_difference by auto using uniques_sound.
    apply app_nil_r.
  Qed.

  Lemma difference_app_l : forall l1 l2 r : list A,
      difference (l1 ∪ l2) r = difference l1 r ∪ difference l2 r.
  Proof.
    intro l1; induction l1 as [| h1 l1 IHl1];
      intros l2 r; simpl; auto.
    rewrite IHl1. apply app_assoc.
  Qed.

  Lemma difference_app_r_comm : forall l r1 r2 : list A,
      difference l (r1 ∪ r2) = difference l (r2 ∪ r1).
  Proof.
    intro l; induction l as [| h l IHl]; intros r1 r2; simpl; auto.
    repeat rewrite member_app_or.
    rewrite orb_comm. rewrite IHl. reflexivity.
  Qed.

  Lemma difference_app_r_assoc : forall l r1 r2 : list A,
      l ∖ r1 ∖ r2 = l ∖ (r1 ∪ r2).
  Proof.
    intro l; induction l as [| h l IHl];
      intros r1 r2; simpl; auto.
    rewrite member_app_or.
    destruct (member h r1) eqn:Hmemhr1; simpl; auto.
    rewrite IHl. reflexivity.
  Qed.

  Local Hint Resolve Permutation_app_comm : core.
  
  Lemma length_uniques_app : forall l r : list A,
      length (uniques (l ++ r)) = length (uniques (r ++ l)).
  Proof.
    intros l r.
    assert (Permutation (uniques (l ++ r)) (uniques (r ++ l)))
      by eauto using uniques_perm.
    auto using Permutation_length.
  Qed.
  
  Local Hint Resolve Union_Subset_l : core.
  Local Hint Resolve Union_Subset_r : core.
  Local Hint Resolve Inter_Subset_l : core.
  Local Hint Resolve Inter_Subset_r : core.
  Local Hint Resolve Diff_Subset : core.
  Local Hint Resolve append_Union : core.
  Local Hint Resolve intersect_Intersection : core.
  Local Hint Resolve difference_Difference : core.
  
  Lemma Subset_union_l : forall l r : list A, l ⊆ l ∪ r.
  Proof.
    eauto.
  Qed.

  Lemma Subset_union_r : forall l r : list A, r ⊆ l ∪ r.
  Proof.
    eauto.
  Qed.

  Lemma Subset_inter_l : forall l r, l ∩ r ⊆ l.
  Proof.
    eauto.
  Qed.

  Lemma Subset_inter_r : forall l r, l ∩ r ⊆ r.
  Proof.
    eauto.
  Qed.

  Lemma Subset_diff : forall l r, l ∖ r ⊆ l.
  Proof.
    eauto.
  Qed.

  Hint Rewrite in_app_iff : core.

  Lemma Subset_l_union : forall l r : list A,
      l ⊆ r -> forall s, l ⊆ r ∪ s.
  Proof.
    unfold Subset; intros.
    autorewrite with core in *; intuition.
  Qed.

  Lemma Subset_r_union : forall l r : list A,
      l ⊆ r -> forall s, l ⊆ s ∪ r.
  Proof.
    unfold Subset; intros.
    autorewrite with core in *; intuition.
  Qed.
  
  Lemma Subset_union_distr_l : forall l r : list A,
      l ⊆ r -> forall s, s ∪ l ⊆ s ∪ r.
  Proof.
    unfold Subset; intros.
    autorewrite with core in *; intuition.
  Qed.

  Lemma Subset_union_distr_r : forall l r : list A,
      l ⊆ r -> forall s, l ∪ s ⊆ r ∪ s.
  Proof.
    unfold Subset; intros.
    autorewrite with core in *; intuition.
  Qed.
  
  Lemma union_perm : forall l r : list A,
      Permutation (l ∪ r) (r ∪ l).
  Proof.
    auto using Permutation_app_comm.
  Qed.
  
  Lemma Inter_nil : forall l r : list A,
      Intersection l r [] -> l ∩ r = [].
  Proof.
    unfold Intersection.
    intro l; induction l as [| a l IHl];
      intros r H; simpl in *; eauto.
    pose proof (In_member_reflects a r) as Har;
      inv Har; simpl in *; firstorder.
  Qed.

  Lemma inter_union_distr : forall l r s,
      l ∩ (r ∪ s) = l ∩ r ∪ l ∩ s.
  Proof.
    intros l;
      induction l as [| h l IHl];
      intros r s; simpl; auto.
    rewrite member_app_or.
    pose proof In_member_reflects h r as Hhr;
      pose proof In_member_reflects h s as Hhs;
      inv Hhr; inv Hhs; simpl; f_equal; auto.
  Abort.

  Lemma uniques_perm_app : forall l l' s,
      Permutation l (l' ++ s) ->
      forall r r',
        Permutation r (r' ++ s) ->
        Permutation (uniques (l ++ r)) (uniques (l' ++ r' ++ s)).
  Proof.
    intros l l' s Hll' r r' Hrr'.
    assert (Happ : Permutation (l ++ r) ((l' ++ s) ++ (r' ++ s)))
      by auto using Permutation_app.
    rewrite <- app_assoc in Happ.
    assert (Happ': Permutation (l ++ r) (l' ++ r' ++ s ++ s)).
    { apply perm_trans with (l' ++ s ++ r' ++ s); auto.
      apply Permutation_app_head.
      apply Permutation_app_swap_app. }
    apply uniques_perm in Happ'.
    rewrite (uniques_app l') in Happ'.
    rewrite (uniques_app r') in Happ'.
    rewrite uniques_app_same in Happ'.
    rewrite <- (uniques_app r') in Happ'.
    rewrite <- (uniques_app l') in Happ'.
    assumption.
  Qed.

  Lemma uniques_uniques_perm_app : forall l l' s,
      Permutation (uniques l) (uniques (l' ++ s)) ->
      forall r r',
        Permutation (uniques r) (uniques (r' ++ s)) ->
        Permutation (uniques (l ++ r)) (uniques (l' ++ r' ++ s)).
  Proof.
    intros l l' s Hll' r r' Hrr'.
    assert (Happ : Permutation
                     (uniques l ++ uniques r)
                     (uniques (l' ++ s) ++ uniques (r' ++ s)))
      by auto using Permutation_app.
    apply uniques_perm in Happ.
    repeat rewrite <- uniques_app in Happ.
    rewrite <- app_assoc in Happ.
    assert (Happ' : Permutation
                      (uniques (l ++ r))
                      (uniques (l' ++ r' ++ s ++ s))).
    { apply perm_trans with (uniques (l' ++ s ++ r' ++ s)); auto.
      apply uniques_perm. apply Permutation_app_head.
      apply Permutation_app_swap_app. }
    rewrite (uniques_app l') in Happ'.
    rewrite (uniques_app r') in Happ'.
    rewrite uniques_app_same in Happ'.
    rewrite <- (uniques_app r') in Happ'.
    rewrite <- (uniques_app l') in Happ'.
    assumption.
  Qed.

  Lemma uniques_uniques_perm_app3 : forall l l' m m' n n' o,
      Permutation (uniques l) (uniques (l' ++ o)) ->
      Permutation (uniques m) (uniques (m' ++ o)) ->
      Permutation (uniques n) (uniques (n' ++ o)) ->
      Permutation (uniques (l ++ m ++ n)) (uniques (l' ++ m' ++ n' ++ o)).
  Proof.
    intros l l' m m' n n' o Hl Hm Hn.
    pose proof uniques_uniques_perm_app _ _ _ Hm _ _ Hn  as Hmn.
    rewrite app_assoc in Hmn.
    pose proof uniques_uniques_perm_app _ _ _ Hl _ _ Hmn as Hml.
    repeat rewrite <- app_assoc in Hml.
    assumption.
  Qed.
End Sets.

Section NatSet.
  Open Scope set_scope.
  Local Hint Constructors Forall : core.

  Lemma list_max_ge : forall l : list nat,
      Forall (fun n => n <= list_max l) l.
  Proof.
    intro l; induction l as [| h t IHt];
      simpl; constructor; try lia.
    apply Forall_forall.
    intros n HIn.
    apply Forall_forall
      with (x:=n) in IHt; try assumption. lia.
  Qed.

  Lemma list_max_ge_in : forall l n,
      n ∈ l -> n <= list_max l.
  Proof.
    intro l. rewrite <- Forall_forall.
    exact (list_max_ge l).
  Qed.
  
  Lemma list_max_succ : forall l : list nat,
    Forall (fun n => n < 1 + list_max l) l.
  Proof.
    intros l. apply Forall_forall.
    pose proof list_max_ge l as H.
    intros n HIn.
    apply Forall_forall
      with (x:=n) in H; try assumption. lia.
  Qed.

  Lemma list_max_succ_not_in : forall l : list nat,
      1 + list_max l ∉ l.
  Proof.
    intros l HIn.
    pose proof list_max_succ l as H.
    pose proof Forall_forall
         (fun n => n < 1 + list_max l) l as [HFF _].
    pose proof HFF H as H'.
    apply H' in HIn. lia.
  Qed.

  Lemma Subset_list_max : forall l r,
      l ⊆ r -> list_max l <= list_max r.
  Proof.
    unfold "⊆".
    intro l; induction l as [| a l IHl];
      intros r HS; simpl in *; try lia.
    destruct (le_gt_dec a (list_max l)) as [Hal | Hal].
    - rewrite max_r by lia; eauto.
    - rewrite max_l by lia.
      assert (Har: In a r) by eauto.
      auto using list_max_ge_in.
  Qed.
End NatSet.
