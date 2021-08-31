Require Export Coq.Lists.List
        Coq.Sorting.Permutation
        CoqRecon.Base Coq.micromega.Lia
        Coq.Arith.Compare_dec.
Export ListNotations.

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
    dispatch_eqdec; firstorder.
  Qed.

  Lemma remove_not_in : forall l a,
      ~ In a l -> remove a l = l.
  Proof.
    intro l; induction l as [| h l IHl];
      intros a H; simpl in *; auto.
    apply Decidable.not_or in H as (Hha & Hal).
    dispatch_eqdec.
    apply IHl in Hal. rewrite Hal. reflexivity.
  Qed.

  Lemma remove_sound : forall l a x,
      In a (remove x l) -> In a l.
  Proof.
    intro l; induction l as [| h l IHl];
      intros a x Hal; simpl in *; auto.
    dispatch_eqdec; firstorder.
  Qed.

  Lemma remove_complete : forall l a x,
      x <> a -> In a l -> In a (remove x l).
  Proof.
    intro l; induction l as [| h l IHl];
      intros a x Hax Hal; simpl in *; auto.
    dispatch_eqdec; destruct Hal; intuition.
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
    eqdec h a; auto.
    destruct Hal; try contradiction.
    eauto using remove_complete.
  Qed.

  Local Hint Constructors NoDup : core.
  Local Hint Resolve remove_sound : core.

  Lemma remove_nodup : forall l,
      NoDup l -> forall a, NoDup (remove a l).
  Proof.
    intros l H; induction H; intros a; simpl; auto.
    dispatch_eqdec; eauto.
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
    specialize IHl with a. dispatch_eqdec; lia.
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
      intros a x; simpl; auto; repeat dispatch_eqdec;
        auto; rewrite IHl; reflexivity.
  Qed.
  
  Lemma remove_uniques_comm : forall l a,
      remove a (uniques l) = uniques (remove a l).
  Proof.
    intro l; induction l as [| h l IHl];
      intro a; simpl; try dispatch_eqdec; auto.
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
      intros r a; simpl; try dispatch_eqdec;
        try rewrite IHl; auto.
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
    dispatch_eqdec; reflexivity.
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
    rewrite IHn.
    destruct n; simpl; try dispatch_eqdec; auto.
  Qed.

  Fixpoint count (a : A) (l : list A) : nat :=
    match l with
    | []    => 0
    | h :: l => (if h == a then 1 else 0) + count a l
    end.

  Lemma count_app : forall l r a,
      count a (l ++ r) = count a l + count a r.
  Proof.
    intro l; induction l as [| h l IHl]; intros r a; simpl; auto.
    rewrite IHl. rewrite PeanoNat.Nat.add_assoc. reflexivity.
  Qed.
  
  Lemma count_remove : forall l a, count a (remove a l) = 0.
  Proof.
    intro l; induction l as [| h l IHl]; intro a; simpl;
      repeat dispatch_eqdec; try rewrite IHl; auto.
  Qed.

  Lemma count_remove_le : forall l a x,
      count a (remove x l) <= count a l.
  Proof.
    intro l; induction l as [| h l IHl]; intros a x; simpl; try lia.
    specialize IHl with (a := a) (x := x).
    repeat dispatch_eqdec; try lia.
  Qed.

  Lemma count_uniques : forall l a,
      count a (uniques l) <= 1.
  Proof.
    intro l; induction l as [| h l IHl]; intro a; simpl; auto.
    specialize IHl with a. dispatch_eqdec.
    - rewrite count_remove. lia.
    - pose proof count_remove_le (uniques l) a h as Hle. lia.
  Qed.

  Lemma count_in : forall l a,
      In a l <-> count a l > 0.
  Proof.
    intro l; induction l as [| h l IHl];
      intro a; simpl; split; intros H;
        try dispatch_eqdec; try firstorder lia.
  Qed.

  Corollary count_uniques_in : forall a l,
      In a l -> count a (uniques l) = 1.
  Proof.
    intros a l Hal.
    rewrite <- uniques_iff in Hal.
    rewrite count_in in Hal.
    pose proof count_uniques l a. lia.
  Qed.
  
  Lemma count_not_in : forall l a,
      ~ In a l <-> count a l = 0.
  Proof.
    intro l; induction l as [| h l IHl];
      intro a; simpl; split; intros H;
        try dispatch_eqdec; try firstorder lia.
  Qed.

  Lemma count_length_le : forall l a,
      count a l <= length l.
  Proof.
    intro l; induction l as [| h l IHl];
      intro a; simpl; try lia.
    specialize IHl with a.
    dispatch_eqdec; lia.
  Qed.
  
  Lemma count_remove_length : forall l a,
      length (remove a l) = length l - count a l.
  Proof.
    intro l; induction l as [| h l IHl]; intro a; simpl;
      repeat dispatch_eqdec; auto.
    destruct (count a l) as [| n] eqn:Hcnt.
    - rewrite <- count_not_in in Hcnt.
      rewrite remove_not_in by assumption. reflexivity.
    - rewrite IHl. rewrite Hcnt.
      pose proof count_length_le l a as HCL. lia.
  Qed.
    
  Lemma count_repeat : forall n a,
      count a (repeat a n) = n.
  Proof.
    intro n; induction n as [| n IHn]; intro a; simpl;
      try dispatch_eqdec; try rewrite IHn; auto.
  Qed.

  Local Hint Constructors Permutation : core.

  Lemma remove_perm : forall l l',
      Permutation l l' -> forall a, Permutation (remove a l) (remove a l').
  Proof.
    intros l l' H; induction H; intro a; simpl;
      repeat dispatch_eqdec; eauto.
  Qed.

  Local Hint Resolve remove_perm : core.
  
  Lemma uniques_perm : forall l l',
      Permutation l l' -> Permutation (uniques l) (uniques l').
  Proof.
    intros l l' H; induction H; simpl; eauto 3.
    rewrite remove_comm. repeat dispatch_eqdec; auto.
  Qed.

  Lemma In_split_repeat_perm : forall l (a : A),
      In a l -> exists n l',
        ~ In a l' /\ Permutation l (repeat a (S n) ++ l').
  Proof.
    intro l; induction l as [| h t IHt];
      intros a Hal; simpl in *; try contradiction.
    destruct (In_dec HEA a t) as [Hat | Hat]; eqdec h a;
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

  (* length l =
     ∑ i ∈ l (count i l) *)
  Lemma length_count_sum : forall l,
      fold_right (fun a acc => count a l + acc) 0 (uniques l) =
      length l.
  Proof.
    intros l; induction l as [| h l IHl]; simpl; auto.
    dispatch_eqdec. f_equal.
    rewrite remove_uniques_comm.
  Abort.
  
  Lemma length_uniques_count : forall l,
      length (uniques l) *
      (fold_right (fun a acc => count a l + acc) 0 l)
      = length l.
  Abort.
End Uniques.
