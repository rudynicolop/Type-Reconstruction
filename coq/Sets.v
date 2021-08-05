Require Export Coq.Classes.EquivDec
        Coq.Lists.List Coq.Bool.Bool
        Coq.Sorting.Permutation
        CoqRecon.Base Coq.micromega.Lia
        Coq.Arith.Compare_dec.
Export ListNotations.

Declare Scope set_scope.
Delimit Scope set_scope with set.

Reserved Notation "l ∪ r" (at level 45, left associativity).
Reserved Notation "l ∩ r" (at level 44, left associativity).
Reserved Notation "l ∖ r" (at level 43, left associativity).

Section Sets.
  Context {A : Set}.
        
  (** [l ⊆ r] *)
  Definition Subset (l r : list A) : Prop :=
    forall a, In a l -> In a r.

  Local Hint Unfold Subset : core.
  Local Hint Resolve Permutation_in : core.
  Local Hint Resolve Permutation_sym : core.

  Lemma Subset_perm_l : forall l l',
      Permutation l l' ->
      forall r, Subset l r -> Subset l' r.
  Proof. eauto. Qed.

  Lemma Subset_perm_r : forall r r',
      Permutation r r' ->
      forall l, Subset l r -> Subset l r'.
  Proof. eauto. Qed.
  
  (** [u] is the union of [l] & [r]. *)
  Definition Union (l r u : list A) : Prop :=
    forall a, In a u <-> In a l \/ In a r.

  Local Hint Unfold Union : core.

  Lemma Union_Subset_l : forall l r u,
      Union l r u -> Subset l u.
  Proof. firstorder. Qed.

  Lemma Union_Subset_r : forall l r u,
      Union l r u -> Subset r u.
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
    forall a, In a i <-> In a l /\ In a r.

  Definition Disjoint (l r : list A) : Prop := Intersection l r [].

  Local Hint Unfold Intersection : core.

  Lemma Inter_Subset_l : forall l r i,
      Intersection l r i -> Subset i l.
  Proof.
    firstorder.
  Qed.

  Lemma Inter_Subset_r : forall l r i,
      Intersection l r i -> Subset i r.
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
    forall a, In a d <-> In a l /\ ~ In a r.

  Local Hint Unfold Difference : core.
  
  Lemma Diff_Subset : forall l r d,
      Difference l r d -> Subset d l.
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
  
  Lemma append_Union : forall l r, Union l r (l ++ r).
  Proof.
    auto using in_app_iff.
  Qed.

  Context {HEA: EqDec A eq}.

  Lemma In_split_repeat_perm : forall l (a : A),
      In a l -> exists n l',
        ~ In a l' /\ Permutation l (repeat a (S n) ++ l').
  Proof.
    intro l; induction l as [| h t IHt];
      intros a Hal; simpl in *; try contradiction.
    destruct (In_dec HEA a t) as [Hat | Hat];
      destruct (equiv_dec h a) as [Hha | Hha];
      unfold equiv, complement in *; subst;
        destruct Hal as [Hha' | Hat']; subst; simpl;
          try contradiction.
    - apply IHt in Hat as (n & l' & Hl' & HP).
      exists (S n). exists l'. simpl; intuition.
    - apply IHt in Hat as (n & l' & Hl' & HP).
      exists (S n). exists l'. simpl; intuition.
    - apply IHt in Hat as (n & l' & Hl' & HP).
      exists n. exists (h :: l'). simpl; intuition.
      rewrite app_comm_cons in *.
      auto using Permutation_cons_app.
    - exists 0. exists t. simpl; intuition.
  Qed.
  
  Fixpoint member (a : A) (l : list A) : bool :=
    match l with
    | [] => false
    | h::t => if a == h then true else member a t
    end.

  Lemma In_member : forall a l, In a l -> member a l = true.
  Proof.
    intros a l; induction l as [| h t IHt];
      intro H; simpl in *;
        [ contradiction | destruct H as [H | H]]; subst;
          match goal with
          | |- context [if equiv_dec ?a ?b then _ else _]
            => destruct (equiv_dec a b);
                unfold equiv in *; subst; auto
          end.
  Qed.

  Local Hint Resolve In_member : core.
  
  Lemma member_In : forall a l, member a l = true -> In a l.
  Proof.
    intros a l; induction l as [| h t IHt];
      intro H; simpl in *; try discriminate.
    destruct (equiv_dec a h) as [Hah | Hah];
      unfold equiv in *; subst; auto.
  Qed.

  Local Hint Resolve member_In : core.
  
  Lemma In_member_reflects : reflects (@In A) member.
  Proof.
    Local Hint Constructors reflect : core.
    unfold reflects.
    intros a l; destruct (member a l) eqn:Hmem; auto.
    constructor. intros H. apply In_member in H.
    rewrite H in Hmem. discriminate.
  Qed.

  Lemma Not_In_member_iff : forall a l,
      member a l = false <-> ~ In a l.
  Proof.
    intros a l.
    pose proof In_member_reflects a l as H.
    inv H; intuition.
  Qed.

  Lemma member_app_or : forall a l r,
      member a (l ++ r) = member a l || member a r.
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

  Fixpoint remove_dups (l : list A) : list A :=
    match l with
    | [] => []
    | a :: l => (if member a l then [] else [a]) ++ remove_dups l
    end.

  Lemma remove_dups_sound : forall l a,
      In a (remove_dups l) -> In a l.
  Proof.
    intro l;
      induction l as [| h t IHt];
      intros a HIn; simpl in *; auto.
    destruct (member h t) eqn:Hmemht; simpl in *; intuition.
  Qed.

  Lemma remove_dups_complete: forall l a,
      In a l -> In a (remove_dups l).
  Proof.
    intro l;
      induction l as [| h t IHt];
      intros a HIn; simpl in *; auto.
    destruct HIn as [Hha | HInat]; subst.
    - destruct (member a t) eqn:Hmemat; simpl; auto.
    - rewrite in_app_iff; auto.
  Qed.

  Local Hint Resolve remove_dups_sound : core.
  Local Hint Resolve remove_dups_complete : core.
  
  Lemma remove_dups_iff : forall a l,
      In a (remove_dups l) <-> In a l.
  Proof.
    intuition.
  Qed.

  Local Hint Constructors NoDup : core.
  
  Lemma remove_dups_NoDup : forall l,
      NoDup (remove_dups l).
  Proof.
    intro l;
      induction l as [| a l IHl]; simpl in *; auto.
    destruct (member a l) eqn:Hmemal; simpl; auto.
    rewrite Not_In_member_iff in Hmemal; auto.
  Qed.

  Lemma remove_dups_length : forall l : list A,
      length (remove_dups l) <= length l.
  Proof.
    intro l; induction l as [| h t IHt];
      simpl; try lia.
    rewrite app_length.
    destruct (member h t) eqn:Hmem; simpl; lia.
  Qed.

  Lemma remove_dups_idempotent : forall l : list A,
      remove_dups (remove_dups l) = remove_dups l.
  Proof.
    intro l; induction l as [| h t IHt]; simpl; auto.
    destruct (member h t) eqn:Hmemht; simpl; auto.
    assert (Hmem': member h (remove_dups t) = false).
    { rewrite Not_In_member_iff in *.
      auto using remove_dups_sound. }
    rewrite Hmem'; simpl; f_equal; assumption.
  Qed.

  Lemma remove_dups_in_split : forall l a,
      In a l ->
      exists l1 l2, ~ In a l1 /\ ~ In a l2 /\
               remove_dups l = remove_dups l1 ++ a :: remove_dups l2.
  Proof.
    intro l; induction l as [| h t IHt];
      intros a Hal; simpl in *; try contradiction.
    pose proof In_member_reflects a t as Hat; inv Hat;
      destruct (equiv_dec h a) as [Hha | Hha];
      unfold equiv, complement in *;
      destruct Hal as [Hal | Hal]; subst;
        try contradiction.
    - apply IHt in H0 as (l1 & l2 & Hl1 & Hl2 & Hrd).
      rewrite <- H; simpl; eauto.
    - apply IHt in Hal as (l1 & l2 & Hl1 & Hl2 & Hrd).
      rewrite <- H; simpl; eauto.
    - apply IHt in Hal as (l1 & l2 & Hl1 & Hl2 & Hrd).
      pose proof In_member_reflects h t as Hht;
        inv Hht; simpl; eauto.
      exists (h :: l1). exists l2. simpl. rewrite Hrd.
      intuition.
      assert (Hmem: member h l1 = false).
      { rewrite Not_In_member_iff.
        intros HIn.
        apply remove_dups_complete in HIn.
        assert (H': In h (remove_dups l1 ++ a :: remove_dups l2)).
        { rewrite in_app_iff. intuition. }
        rewrite <- Hrd in H'.
        apply remove_dups_sound in H'.
        contradiction. }
      rewrite Hmem; simpl. reflexivity.
    - rewrite <- H. exists []. exists t. intuition.
  Qed.

  Lemma remove_dups_disjoint_app : forall l r : list A,
      Disjoint l r ->
      remove_dups (l ++ r) =
      remove_dups l ++ remove_dups r.
  Proof.
    unfold Disjoint, Intersection.
    intro l; induction l as [| a l IHl];
      intros r Hd; simpl in *; auto.
    rewrite member_app_or.
    pose proof In_member_reflects a l as Hal; inv Hal; simpl.
    - apply IHl. intros a'.
      specialize Hd with a'. intuition.
    - pose proof In_member_reflects a r as Har; inv Har; simpl.
      + admit.
      + f_equal. apply IHl. intros a'.
        specialize Hd with a'. intuition.
  Abort.
  
  Lemma remove_dups_app : forall l r : list A,
      remove_dups (l ++ r) =
      remove_dups (remove_dups l ++ remove_dups r).
  Proof.
    intro l; induction l as [| a l IHl]; intro r; simpl.
    - rewrite remove_dups_idempotent; reflexivity.
    - pose proof (In_member_reflects a l) as Hal; inv Hal; simpl.
      + assert (Halr: member a (l ++ r) = true).
        { apply In_member.
          rewrite in_app_iff. intuition. }
        rewrite Halr; simpl; auto.
      + pose proof (In_member_reflects a r) as Har; inv Har; simpl.
        * assert (Halr: member a (l ++ r) = true).
          { apply In_member.
            rewrite in_app_iff. intuition. }
          rewrite Halr; simpl.
          assert (Halr': member a (remove_dups l ++ remove_dups r) = true).
          { apply In_member. rewrite in_app_iff.
            auto using remove_dups_complete. }
          rewrite Halr'; simpl; auto.
        * assert (Halr: member a (l ++ r) = false).
          { rewrite Not_In_member_iff.
            rewrite in_app_iff. intuition. }
          rewrite Halr; simpl.
          assert (Halr': member a (remove_dups l ++ remove_dups r) = false).
          { apply Not_In_member_iff. rewrite in_app_iff.
            Local Hint Resolve remove_dups_sound : core.
            intuition. }
          rewrite Halr'; simpl; f_equal; auto.
  Qed.

  Lemma remove_dups_app_length : forall l r : list A,
      length (remove_dups (l ++ r)) <=
      length (remove_dups l) + length (remove_dups r).
  Proof.
    intro l; induction l as [| a l IHl]; intro r; simpl; try lia.
    repeat rewrite app_length.
    pose proof (In_member_reflects a l) as Hal; inv Hal; simpl.
    - assert (Halr: member a (l ++ r) = true).
      { apply In_member. rewrite in_app_iff. intuition. }
      rewrite Halr; simpl; auto.
    - pose proof (In_member_reflects a (l ++ r)) as Halr;
        inv Halr; simpl; pose proof IHl r; lia.
  Qed.

  Lemma remove_dups_length_perm : forall l l',
      Permutation l l' ->
      length (remove_dups l) = length (remove_dups l').
  Proof.
    intros l l' HP; induction HP; simpl; try lia.
    - repeat rewrite app_length. rewrite IHHP.
      pose proof In_member_reflects x l as Hxl; inv Hxl.
      + assert (HIn: In x l') by eauto.
        assert (Hmem: member x l' = true) by auto.
        rewrite Hmem. reflexivity.
      + assert (HIn: ~ In x l') by eauto.
        rewrite <- Not_In_member_iff in HIn.
        rewrite HIn. reflexivity.
    - repeat rewrite app_length.
      destruct (equiv_dec y x) as [Hyx | Hyx];
        destruct (equiv_dec x y) as [Hxy | Hxy];
        unfold equiv, complement in *;
        subst; try contradiction; simpl; try lia.
  Qed.

  Lemma member_repeat : forall n a,
      member a (repeat a n) =
      match n with
      | O => false
      | S _ => true
      end.
  Proof.
    intros [| n] a; simpl; auto.
    destruct (equiv_dec a a);
      unfold equiv, complement in *; try contradiction; auto.
  Qed.

  Lemma remove_dups_repeat : forall n a,
      remove_dups (repeat a n) =
      match n with
      | O => []
      | S _ => [a]
      end.
  Proof.
    intro n; induction n as [| n IHn]; intro a; simpl; auto.
    rewrite member_repeat, IHn.
    destruct n; reflexivity.
  Qed.

  Lemma remove_dups_length_app_l : forall l r,
      length (remove_dups l) <= length (remove_dups (l ++ r)).
  Proof.
    intro l; induction l as [| a l IHl];
      intros r; simpl; try lia.
    rewrite member_app_or.
    destruct (member a l) eqn:Hal; simpl; auto.
    destruct (member a r) eqn:Har; simpl.
    - assert (HInar: In a r) by auto.
      apply In_split_repeat_perm in HInar
        as (n & r' & Hr' & HP).
      rewrite remove_dups_length_perm
        with (l := l ++ r)
             (l' := repeat a (S n) ++ l ++ r').
      + rewrite remove_dups_app.
        rewrite remove_dups_repeat; simpl.
        assert (H': ~ In a (remove_dups (l ++ r'))).
        { intros H'. apply remove_dups_sound in H'.
          rewrite in_app_iff in H'. intuition.
          rewrite Not_In_member_iff in Hal.
          contradiction. }
        rewrite <- Not_In_member_iff in H'.
        rewrite H'. rewrite app_length; simpl.
        rewrite remove_dups_idempotent.
        specialize IHl with (r := r'). lia.
      + apply perm_trans
          with (l' := l ++ (repeat a (S n) ++ r')).
        * auto using Permutation_app_head.
        * auto using Permutation_app_swap_app.
    - specialize IHl with r. lia.
  Qed.

  Lemma remove_dups_length_app_r : forall l r,
      length (remove_dups r) <= length (remove_dups (l ++ r)).
  Proof.
    intros l r.
    rewrite remove_dups_length_perm
      with (l := l ++ r) (l' := r ++ l)
      by auto using Permutation_app_comm.
    apply remove_dups_length_app_l.
  Qed.
  
  Fixpoint intersect (l r : list A) : list A :=
    match l with
    | [] => []
    | h::t =>
      (if member h r then [h] else []) ++ intersect t r
    end.

  Lemma intersect_Intersection : forall l r,
      Intersection l r (intersect l r).
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

  Fixpoint difference (l r : list A) : list A :=
    match l with
    | [] => []
    | h::t =>
      (if member h r then [] else [h]) ++ difference t r
    end.

  Lemma difference_Difference : forall l r,
      Difference l r (difference l r).
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

  Local Hint Resolve Union_Subset_l : core.
  Local Hint Resolve Union_Subset_r : core.
  Local Hint Resolve Inter_Subset_l : core.
  Local Hint Resolve Inter_Subset_r : core.
  Local Hint Resolve Diff_Subset : core.
  Local Hint Resolve append_Union : core.
  Local Hint Resolve intersect_Intersection : core.
  Local Hint Resolve difference_Difference : core.
  
  Lemma Subset_union_l : forall l r, Subset l (l ++ r).
  Proof.
    eauto.
  Qed.

  Lemma Subset_union_r : forall l r, Subset r (l ++ r).
  Proof.
    eauto.
  Qed.

  Lemma Subset_inter_l : forall l r, Subset (intersect l r) l.
  Proof.
    eauto.
  Qed.

  Lemma Subset_inter_r : forall l r, Subset (intersect l r) r.
  Proof.
    eauto.
  Qed.

  Lemma Subset_diff : forall l r, Subset (difference l r) l.
  Proof.
    eauto.
  Qed.
End Sets.

Notation "l ⊆ r"
  := (Subset l r)
       (at level 80, no associativity) : set_scope.
Notation "l ∪ r" := (l ++ r) : set_scope.
Notation "l ∩ r" := (intersect l r) : set_scope.
Notation "l ∖ r" := (difference l r) : set_scope.

Section SubsetUnion.
  Open Scope set_scope.

  Context {A : Set}.

  Hint Rewrite in_app_iff : core.
  Local Hint Unfold Subset : core.

  Lemma Subset_cons : forall l r : list A,
      l ⊆ r -> forall a : A, a :: l ⊆ a :: r.
  Proof.
    unfold Subset; intros;
      simpl in *; intuition.
  Qed.

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
End SubsetUnion.

Section InterNil.
  Open Scope set_scope.

  Context {A : Set}.
  Context {HEA: EqDec A eq}.
  
  Lemma Inter_nil : forall l r : list A,
      Intersection l r [] -> l ∩ r = [].
  Proof.
    unfold Intersection.
    intro l; induction l as [| a l IHl];
      intros r H; simpl in *; eauto.
    pose proof (In_member_reflects a r) as Har;
      inv Har; simpl in *; firstorder.
  Qed.
End InterNil.

Section NatSet.
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
      In n l -> n <= list_max l.
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
      ~ In (1 + list_max l) l.
  Proof.
    intros l HIn.
    pose proof list_max_succ l as H.
    pose proof Forall_forall
         (fun n => n < 1 + list_max l) l as [HFF _].
    pose proof HFF H as H'.
    apply H' in HIn. lia.
  Qed.

  Open Scope set_scope.

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
