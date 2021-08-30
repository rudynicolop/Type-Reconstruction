Require Export Coq.Classes.EquivDec
        Coq.Lists.List Coq.Bool.Bool
        Coq.Sorting.Permutation
        CoqRecon.Base Coq.micromega.Lia
        Coq.Arith.Compare_dec.
Export ListNotations.
Require Import Coq.funind.Recdef.

Declare Scope set_scope.
Delimit Scope set_scope with set.

Reserved Notation "l ∪ r" (at level 45, left associativity).
Reserved Notation "l ∩ r" (at level 44, left associativity).
Reserved Notation "l ∖ r" (at level 43, left associativity).

Section Uniques.
  Context {A : Set}.
  Context {HEA: EqDec A eq}.

  Fixpoint remove (a : A) (l : list A) : list A :=
    match l with
    | []    => []
    | h :: l => (if h == a then [] else [h]) ++ remove a l
    end.

  Lemma remove_correct : forall l a, ~ In a (remove a l).
  Proof.
    intro l; induction l as [| h l IHl];
      intros a H; simpl in *; auto.
    destruct (equiv_dec h a) as [Hha | Hha];
      unfold equiv, complement in *; subst; simpl in *; firstorder.
  Qed.

  Lemma remove_not_in : forall l a,
      ~ In a l -> remove a l = l.
  Proof.
    intro l; induction l as [| h l IHl];
      intros a H; simpl in *; auto.
    apply Decidable.not_or in H as (Hha & Hal).
    destruct (equiv_dec h a) as [? | _];
      unfold equiv, complement in *; subst; simpl in *; try contradiction.
    apply IHl in Hal. rewrite Hal. reflexivity.
  Qed.

  Lemma remove_sound : forall l a x,
      In a (remove x l) -> In a l.
  Proof.
    intro l; induction l as [| h l IHl];
      intros a x Hal; simpl in *; auto.
    destruct (equiv_dec h x) as [Hhx | Hhx];
      unfold equiv, complement in *; subst; simpl in *; firstorder.
  Qed.

  Lemma remove_complete : forall l a x,
      x <> a -> In a l -> In a (remove x l).
  Proof.
    intro l; induction l as [| h l IHl];
      intros a x Hax Hal; simpl in *; auto.
    destruct (equiv_dec h x) as [Hhx | Hhx];
      unfold equiv, complement in *; subst; simpl in *;
        destruct Hal; intuition.
  Qed.

  Fixpoint uniques (l : list A) : list A :=
    match l with
    | []    => []
    | a :: l => a :: remove a (uniques l)
    end.
  
  Lemma uniques_sound : forall l a,
      In a (uniques l) -> In a l.
  Proof.
    intro l; induction l as [| h l IHl];
      intros a Hal; simpl in *; auto.
    destruct Hal as [Hha | Hal]; eauto using remove_sound.
  Qed.

  Lemma uniques_complete : forall l a,
      In a l -> In a (uniques l).
  Proof.
    intro l; induction l as [| h l IHl];
      intros a Hal; simpl in *; auto.
    destruct (equiv_dec h a) as [Hha | Hha];
      unfold equiv, complement in *; subst; auto.
    destruct Hal; try contradiction.
    eauto using remove_complete.
  Qed.

  Local Hint Constructors NoDup : core.
  Local Hint Resolve remove_sound : core.

  Lemma remove_nodup : forall l,
      NoDup l -> forall a, NoDup (remove a l).
  Proof.
    intros l H; induction H; intros a; simpl; auto.
    destruct (equiv_dec x a) as [Hxa | Hxa];
      unfold equiv, complement in *; subst; simpl in *; eauto.
  Qed.

  Local Hint Resolve remove_correct : core.
  Local Hint Resolve remove_nodup : core.
  
  Lemma uniques_nodup : forall l,
      NoDup (uniques l).
  Proof.
    intro l; induction l as [| a l IHl]; simpl; auto.
  Qed.

  Local Hint Resolve uniques_sound : core.
  Local Hint Resolve uniques_complete : core.

  Lemma uniques_iff : forall a l,
      In a (uniques l) <-> In a l.
  Proof.
    intuition.
  Qed.

  Lemma remove_length : forall l a,
      length (remove a l) <= length l.
  Proof.
    intro l; induction l as [| h l IHl];
      intro a; simpl; auto.
    rewrite app_length.
    specialize IHl with a.
    destruct (equiv_dec h a); simpl; lia.
  Qed.

  Lemma uniques_length : forall l,
      length (uniques l) <= length l.
  Proof.
    intro l; induction l as [| a l IHl]; simpl in *; auto.
    pose proof remove_length (uniques l) a. lia.
  Qed.

  Lemma remove_idempotent : forall l a,
      remove a (remove a l) = remove a l.
  Proof.
    intros l a.
    rewrite remove_not_in with (l := remove a l) by auto.
    reflexivity.
  Qed.

  Lemma remove_comm : forall l a x,
      remove a (remove x l) = remove x (remove a l).
  Proof.
    intro l; induction l as [| h l IHl];
      intros a x; simpl; auto.
    destruct (equiv_dec h x) as [Hhx | Hhx];
      destruct (equiv_dec h a) as [Hha | Hha];
      unfold equiv, complement in *; subst; simpl; auto.
    - destruct (equiv_dec x x);
        unfold equiv, complement in *; simpl; intuition.
    - destruct (equiv_dec a a);
        unfold equiv, complement in *; simpl; intuition.
    - destruct (equiv_dec h x); destruct (equiv_dec h a);
        unfold equiv, complement in *;
        subst; simpl; try contradiction; auto.
      rewrite IHl. reflexivity.
  Qed.
  
  Lemma remove_uniques_comm : forall l a,
      remove a (uniques l) = uniques (remove a l).
  Proof.
    intro l; induction l as [| h l IHl];
      intro a; simpl; auto.
    destruct (equiv_dec h a) as [Hha | Hha];
      unfold equiv, complement in *; subst; simpl.
    - rewrite remove_idempotent; auto.
    - rewrite remove_comm. rewrite IHl.
      reflexivity.
  Qed.

  Lemma uniques_idempotent : forall l,
      uniques (uniques l) = uniques l.
  Proof.
    intro l; induction l as [| a l IHl]; simpl; auto.
    repeat rewrite <- remove_uniques_comm.
    rewrite remove_idempotent. rewrite IHl.
    reflexivity.
  Qed.

  Lemma remove_app : forall l r a,
      remove a (l ++ r) = remove a l ++ remove a r.
  Proof.
    intro l; induction l as [| h l IHl];
      intros r a; simpl; auto.
    destruct (equiv_dec h a) as [Hha | Hha];
      unfold equiv, complement in *; subst; simpl;
        rewrite IHl; reflexivity.
  Qed.
  
  Lemma uniques_app : forall l r,
      uniques (l ++ r) = uniques (uniques l ++ uniques r).
  Proof.
    intro l; induction l as [| h l IHl];
      intro r; simpl.
    - rewrite uniques_idempotent. reflexivity.
    - f_equal. rewrite IHl.
      repeat rewrite remove_uniques_comm.
      repeat rewrite remove_app.
      rewrite <- remove_uniques_comm.
      rewrite remove_idempotent. reflexivity.
  Qed.

  Lemma remove_rev : forall l a,
      rev (remove a l) = remove a (rev l).
  Proof.
    intro l; induction l as [| h l IHl];
      intro a; simpl; auto.
    repeat rewrite remove_app; simpl.
    rewrite rev_app_distr.
    rewrite IHl. f_equal.
    destruct (equiv_dec h a); reflexivity.
  Qed.
  
  Lemma uniques_app2 : forall l r,
      uniques (l ++ r) = uniques l ++ fold_right remove (uniques r) l.
  Proof.
    intro l; induction l as [| h l IHl];
      intro r; simpl; auto.
    f_equal. rewrite IHl.
    rewrite remove_app. reflexivity.
  Qed.

  Lemma uniques_repeat : forall n a,
      uniques (repeat a n) =
      match n with
      | O   => []
      | S _ => [a]
      end.
  Proof.
    intro n; induction n as [| n IHn];
      intro a; simpl; auto.
    rewrite IHn. destruct n; simpl; auto.
    destruct (equiv_dec a a);
      unfold equiv, complement in *; try contradiction; auto.
  Qed.
End Uniques.

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

  Lemma Subset_Diff : forall l r,
      Subset l r ->
      Difference l r [].
  Proof.
    unfold Subset, Difference.
    intros l r Hs a; simpl; intuition.
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

  Lemma diff_empty_r : forall l : list A,
      difference l [] = l.
  Proof.
    intro l; induction l as [| h l]; simpl; auto.
    rewrite IHl. reflexivity.
  Qed.

  Lemma remove_diff_cons : forall l r a,
      difference l (a :: r) = remove a (difference l r).
  Proof.
    intro l; induction l as [| h l IHl];
      intros r a; simpl; auto.
    destruct (equiv_dec h a) as [Hha | Hha];
      unfold equiv, complement in *;
      destruct (member h r) eqn:Hmemhr; subst; simpl; auto.
    - destruct (equiv_dec a a);
        unfold equiv, complement in *;
        try contradiction; simpl; auto.
    - destruct (equiv_dec h a);
        unfold equiv, complement in *;
        try contradiction; simpl; f_equal; auto.
  Qed.
  
  Lemma remove_diff : forall l r : list A,
      fold_right remove l r = difference l r.
  Proof.
    intro l; induction l as [| a l IHl];
      intro r; induction r as [| x r IHr]; simpl in *; auto.
    - rewrite IHr. reflexivity.
    - f_equal. rewrite diff_empty_r. reflexivity.
    - destruct (equiv_dec a x) as [Hax | Hax];
        unfold equiv, complement in *; subst; simpl.
      + rewrite IHr. rewrite remove_app.
        destruct (member x r); simpl.
        * rewrite remove_diff_cons. reflexivity.
        * destruct (equiv_dec x x);
            unfold equiv, complement in *; try contradiction; simpl.
          rewrite remove_diff_cons. reflexivity.
      + destruct (member a r) eqn:Hmemar; simpl in *.
        * rewrite IHr. rewrite remove_diff_cons. reflexivity.
        * rewrite IHr; simpl.
          destruct (equiv_dec a x);
            unfold equiv, complement in *;
            try contradiction; simpl; f_equal.
          rewrite remove_diff_cons. reflexivity.
  Qed.

  Lemma Subset_difference : forall l r,
      Subset l r -> difference l r = [].
  Proof.
    intros l r Hlr. apply Subset_Diff in Hlr.
    unfold Difference in Hlr.
    induction l as [| h l IHl]; simpl; auto.
    pose proof In_member_reflects h r as Hhr; inv Hhr; simpl; firstorder.
  Qed.

  Corollary difference_same : forall l : list A,
      difference l l = [].
  Proof.
    intros l. apply Subset_difference.
    intuition.
  Qed.

  Corollary uniques_app_same : forall l : list A,
      uniques (l ++ l) = uniques l.
  Proof.
    intros l. rewrite uniques_app2.
    rewrite remove_diff.
    rewrite Subset_difference by auto using uniques_sound.
    apply app_nil_r.
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
