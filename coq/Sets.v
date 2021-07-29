Require Export Coq.Classes.EquivDec
        Coq.Lists.List Coq.Bool.Bool
        Coq.Sorting.Permutation
        CoqRecon.Base Coq.micromega.Lia.
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

  Lemma Subset_perm_l : forall l l',
      Permutation l' l ->
      forall r, Subset l r -> Subset l' r.
  Proof.
    eauto using Permutation_in.
  Qed.

  Lemma Subset_perm_r : forall r r',
      Permutation r r' ->
      forall l, Subset l r -> Subset l r'.
  Proof.
    eauto using Permutation_in.
  Qed.
  
  (** [u] is the union of [l] & [r]. *)
  Definition Union (l r u : list A) : Prop :=
    forall a, In a u <-> In a l \/ In a r.

  Local Hint Unfold Union : core.

  Lemma Union_Subset_l : forall l r u,
      Union l r u -> Subset l u.
  Proof.
    firstorder.
  Qed.

  Lemma Union_Subset_r : forall l r u,
      Union l r u -> Subset r u.
  Proof.
    firstorder.
  Qed.

  (** [i] is the intersection of [l] & [r]. *)
  Definition Intersection (l r i : list A) : Prop :=
    forall a, In a i <-> In a l /\ In a r.

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
  
  (** [d] is the diff of [l] & [r]. *)
  Definition Difference (l r d : list A) : Prop :=
    forall a, In a d <-> In a l /\ ~ In a r.

  Local Hint Unfold Difference : core.
  
  Lemma Diff_Subset : forall l r d,
      Difference l r d -> Subset d l.
  Proof.
    firstorder.
  Qed.
  
  Lemma append_Union : forall l r, Union l r (l ++ r).
  Proof.
    auto using in_app_iff.
  Qed.

  Context {HEA: EqDec A eq}.

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
    
  Fixpoint intersect (l r : list A) : list A :=
    match l with
    | [] => []
    | h::t =>
      (if member h r then [h] else []) ++ intersect t r
    end.

  Lemma Intersection_intersect : forall l r,
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

  Lemma Difference_difference : forall l r,
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
  Local Hint Resolve Intersection_intersect : core.
  Local Hint Resolve Difference_difference : core.
  
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

Section NatSet.
  Local Hint Constructors Forall : core.

  Search list_max.
  
  Lemma list_max_succ : forall l : list nat,
    Forall (fun n => n < 1 + list_max l) l.
  Proof.
    Search list_max.
    intro l; induction l as [| h t IHt]; auto.
    constructor.
  Abort.
End NatSet.
