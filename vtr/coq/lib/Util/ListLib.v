Require Export Coq.Lists.List
        Coq.Sorting.Permutation
        CoqRecon.Util.Base Coq.micromega.Lia
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

  Lemma length_uniques_app_le : forall l r,
      length (uniques l) <= length (uniques (l ++ r)).
  Proof.
    intros l r.
    rewrite uniques_app2.
    rewrite app_length. lia.
  Qed.

  Lemma uniques_Forall : forall P l,
      Forall P (uniques l) <-> Forall P l.
  Proof.
    intros P l; repeat rewrite Forall_forall; intuition.
  Qed.
End Uniques.

Section Inside.
  Context {A : Set}.
  
  Inductive inside (a : A) : list A -> Prop :=
  | inside_cons_hd t :
      inside a (a :: t)
  | inside_cons_tl h t :
      h <> a ->
      inside a t ->
      inside a (h :: t).

  Lemma inside_sound : forall a l, inside a l -> In a l.
  Proof.
    intros a l H; induction H; intuition.
  Qed.
    
  Lemma inside_split_first : forall a l,
      inside a l -> exists l1 l2, l = l1 ++ a :: l2 /\ ~ inside a l1.
  Proof.
    intros a l H; induction H.
    - exists [], t. split; auto.
      intros H; inv H.
    - destruct IHinside as (l1 & l2 & Ht & Hl1); subst.
      exists (h :: l1), l2. split; auto.
      intros Hin; inv Hin; contradiction.
  Qed.

  Hypothesis Hexm_eq : forall a1 a2 : A, a1 = a2 \/ a1 <> a2.

  Local Hint Constructors inside : core.

  Lemma inside_complete : forall l a, In a l -> inside a l.
  Proof.
    intro l; induction l as [| h t IHt];
      intros a Hal; simpl in *; try contradiction.
    destruct (Hexm_eq h a) as [Hha | Hha];
      firstorder subst; auto.
  Qed.

  Local Hint Resolve inside_sound : core.
  Local Hint Resolve inside_complete : core.

  Lemma inside_in_iff : forall a l,
      inside a l <-> In a l.
  Proof.
    intuition.
  Qed.

  Lemma inside_in_not_iff : forall a l,
      ~ inside a l <-> ~ In a l.
  Proof.
    intuition.
  Qed.
  
  Lemma in_split_first : forall (a : A) l,
      In a l -> exists l1 l2, l = l1 ++ a :: l2 /\ ~ In a l1.
  Proof.
    intros a l HIn.
    apply inside_complete in HIn.
    apply inside_split_first in HIn
      as (l1 & l2 & Hl & Hl1); subst.
    exists l1, l2; auto.
  Qed.
End Inside.

Fixpoint flipper {A B : Set} (C : list (A * B)) : list (B * A) :=
  match C with
  | []         => []
  | (l, r) :: C => (r, l) :: flipper C
  end.

Lemma flipper_involutive : forall (A B : Set) (C : list (A * B)),
    flipper (flipper C) = C.
Proof.
  intros A B C; induction C as [| [l r] C IHC]; simpl; f_equal; auto.
Qed.

Lemma flipper_nil : forall (A B : Set) (C : list (A * B)),
    flipper C = [] -> C = [].
Proof.
  intros A B C HC.
  destruct C as [| [? ?] ?];
    simpl in *; try discriminate; reflexivity.
Qed.

Lemma in_flipper : forall (A B : Set) l (a : A) (b : B),
    In (a, b) l -> In (b, a) (flipper l).
Proof.
  intros A B l; induction l as [| [u v] l IHl];
    intros a b Hin; simpl in *; auto.
  destruct Hin as [Hab | Hab]; try inv Hab; auto.
Qed.

Section PairLists.
  Context {U V : Set}.

  Lemma combine_map_fst : forall (us : list U) (vs : list V),
      map fst (combine us vs) = firstn (min (length us) (length vs)) us.
  Proof.
    intro us; induction us as [| u us IHus];
      intros [| v vs]; simpl; f_equal; auto.
  Qed.

  Lemma combine_map_snd : forall (vs : list V) (us : list U),
      map snd (combine us vs) = firstn (min (length us) (length vs)) vs.
  Proof.
    intro vs; induction vs as [| v vs IHvs];
    intros [| u us]; simpl; f_equal; auto.
  Qed.

  Lemma split_map : forall (l : list (U * V)),
      split l = (map fst l, map snd l).
  Proof.
    intro l; induction l as [| [u v] t IHt]; simpl; auto.
    destruct (split t) as [us vs] eqn:Hsplit; simpl; inv IHt; auto.
  Qed.

  Lemma combine_map : forall (l : list (U * V)),
      combine (map fst l) (map snd l) = l.
  Proof.
    intros l.
    pose proof split_combine l as H.
    destruct (split l) as [us vs] eqn:Hsplit.
    rewrite split_map in Hsplit.
    injection Hsplit as Hus Hvs.
    rewrite Hus, Hvs; assumption.
  Qed.
  
  Hint Rewrite map_length : core.
  Local Hint Resolve combine_map : core.
           
  Lemma combine_ex : forall (l : list (U * V)),
      exists us vs, l = combine us vs /\ length us = length vs.
  Proof.
    intro l. exists (map fst l). exists (map snd l).
    autorewrite with core; auto.
  Qed.

  Lemma flipper_combine : forall (us : list U) (vs : list V),
      flipper (combine us vs) = combine vs us.
  Proof.
    intro us; induction us as [| u us IHus];
      intros [| v vs]; simpl; f_equal; auto.
  Qed.

  Local Hint Constructors NoDup : core.
  
  Lemma NoDup_combine : forall (us : list U),
      NoDup us ->
      forall (vs : list V),
        NoDup (combine us vs).
  Proof.
    intros us Hndu; induction Hndu;
      intros [| v vs]; simpl; auto.
    assert (~ In (x, v) (combine l vs)).
    { intros Hin.
      apply in_combine_l in Hin as ?; contradiction. }
    auto.
  Qed.

  Lemma NoDup_pair_eq_r : forall us,
      NoDup us ->
      forall vs (u : U) (v1 v2 : V),
        In (u,v1) (combine us vs) ->
        In (u,v2) (combine us vs) ->
        v1 = v2.
  Proof.
    intros us Hnd; induction Hnd;
      intros [| v vs] u v1 v2 Hv1 Hv2;
      simpl in *; try contradiction.
    destruct Hv1 as [Hv1 | Hv1];
      destruct Hv2 as [Hv2 | Hv2]; subst;
        try inv Hv1; try inv Hv2; eauto;
          try apply in_combine_l in Hv2;
          try apply in_combine_l in Hv1; contradiction.
  Qed.

  Lemma NoDup_pair_eq_l : forall vs,
      NoDup vs ->
      forall us (u1 u2 : U) (v : V),
        In (u1,v) (combine us vs) ->
        In (u2,v) (combine us vs) ->
        u1 = u2.
  Proof.
    intros vs Hnd; induction Hnd;
      intros [| u us] u1 u2 v Hin1 Hin2;
      simpl in *; try contradiction.
    destruct Hin1 as [Hu1 | Hin1];
      destruct Hin2 as [Hu2 | Hin2];
      try inv Hu1; try inv Hu2; eauto;
        try apply in_combine_r in Hin2;
        try apply in_combine_r in Hin1; contradiction.
  Qed.

  Lemma in_combine_nth_error : forall us vs (u : U) (v : V),
      In (u,v) (combine us vs) ->
      exists n, nth_error us n = Some u /\ nth_error vs n = Some v.
  Proof.
    intro us; induction us as [| hu us IHus];
      intros [| hv vs] u v Hin; simpl in *;
        try contradiction.
    destruct Hin as [Hin | Hin]; try inv Hin.
    - exists 0; auto.
    - apply IHus in Hin as (n & Hus & Hvs).
      exists (S n); auto.
  Qed.

  Lemma nth_error_combine_some : forall n us vs (u : U) (v : V),
      nth_error us n = Some u ->
      nth_error vs n = Some v ->
      nth_error (combine us vs) n = Some (u, v).
  Proof.
    intro n; induction n as [| n IHn];
      intros [| hu us] [| hv vs] u v Hu Hv;
      simpl in *; inv Hu; inv Hv; auto.
  Qed.
  
  Local Hint Resolve nth_error_combine_some : core.

  Lemma in_combine_index : forall n us vs (u : U) (v : V),
      nth_error us n = Some u ->
      nth_error vs n = Some v ->
      In (u,v) (combine us vs).
  Proof.
    intros n us vs u v Hu Hv.
    eauto using nth_error_In.
  Qed.

  Context {HEU : EqDec U eq} {HEV : EqDec V eq}.
  
  Lemma not_in_combine : forall us vs (u : U) (v : V),
      ~ In (u,v) (combine us vs) ->
      ~ In u us /\ ~ In v vs \/
      In u us   /\ ~ In v vs \/
      ~ In u us /\   In v vs \/
      exists m n, m <> n /\ nth_error us m = Some u /\ nth_error vs n = Some v.
  Proof.
    intros us vs u v Hin.
    pose proof in_dec HEU u us as [Huus | Huus];
      pose proof in_dec HEV v vs as [Hvvs | Hvvs]; auto.
    apply In_nth_error in Huus, Hvvs.
    destruct Huus as [p Hus]; destruct Hvvs as [q Hvs].
    repeat right. exists p, q; intuition; subst.
    apply Hin. apply nth_error_In with q; auto.
  Qed.
End PairLists.

Lemma nodup_triple_eq_r : forall {U V W : Set} us,
    NoDup us ->
    forall (u : U) (v : V) (w1 w2 : W) vs ws,
      NoDup vs ->
      In (u,v) (combine us vs) ->
      In (u,w1) (combine us ws) ->
      In (v,w2) (combine vs ws) -> w1 = w2.
Proof.
  intros U V W us Hndus;
    induction Hndus as [| hu us Hninu Hndus IHus];
    intros u v w1 w2 vs [| w ws] Hndvs Huv Huw Hvw;
    inversion Hndvs as [Hvsnil | hv tvs Hninhv Hndtvs]; subst;
      simpl in *; try contradiction.
  destruct Huv as [Huv | Huv];
    destruct Huw as [Huw | Huw];
    destruct Hvw as [Hvw | Hvw];
    try inv Huv; try inv Huw; try inv Hvw; eauto;
      try apply in_combine_l in Hvw;
      try apply in_combine_l in Huw;
      try apply in_combine_l in Huv as Hu';
      try apply in_combine_r in Huv as Hv';
      contradiction.
Qed.

Lemma flipper_combine_map_fst : forall {U V : Set} (us : list U) (vs : list V),
    map fst (flipper (combine us vs)) =
    firstn (min (length us) (length vs)) vs.
Proof.
  intros U V us vs.
  rewrite flipper_combine.
  rewrite combine_map_fst.
  f_equal. lia.
Qed.

Lemma flipper_combine_map_snd : forall {U V : Set} (us : list U) (vs : list V),
    map snd (flipper (combine us vs)) =
    firstn (min (length us) (length vs)) us.
Proof.
  intros U V us vs.
  rewrite flipper_combine.
  rewrite combine_map_snd.
  f_equal; lia.
Qed.

Lemma combine_map_l :
  forall {U V W : Set} (f : U -> W) (us : list U) (vs : list V),
    combine (map f us) vs = map (fun '(u,v) => (f u,v)) (combine us vs).
Proof.
  intros U V W f us; induction us as [| u us IHus];
    intros [| v vs]; simpl; f_equal; auto.
Qed.

Lemma combine_map_r :
  forall {U V W : Set} (f : V -> W) (us : list U) (vs : list V),
    combine us (map f vs) = map (fun '(u,v) => (u,f v)) (combine us vs).
Proof.
  intros U V W f us; induction us as [| u us IHus];
    intros [| v vs]; simpl; f_equal; auto.
Qed.

Lemma in_combine_flip :
  forall {U V : Set} us vs (u : U) (v : V),
    In (u,v) (combine us vs) -> In (v,u) (combine vs us).
Proof.
  intros U V us; induction us as [| hu us IHus];
    intros [| hv vs] u v Hin; simpl in *;
      try contradiction.
  destruct Hin as [Huv | Hin]; try inv Huv; auto.
Qed.

Lemma nodup_nth_error : forall (A : Set) l,
    NoDup l ->
    forall m n (a : A),
      nth_error l m = Some a ->
      nth_error l n = Some a -> m = n.
Proof.
  intros A l Hnd; induction Hnd;
    intros [| m] [| n] h Hm Hn; simpl in *;
      try discriminate; auto.
  - inv Hm; apply nth_error_In in Hn; contradiction.
  - inv Hn; apply nth_error_In in Hm; contradiction.
  - f_equal; eauto.
Qed.

(** My contribution to the standard library. *)
Section CuttingMap.
  Context {A B : Set}.
  Variable (f : A -> B).
  
  Lemma firstn_map : forall n l,
      firstn n (map f l) = map f (firstn n l).
  Proof.
    intro n; induction n as [| n IHn];
      intros [| a l]; simpl in *; f_equal; auto.
  Qed.

  Lemma skipn_map : forall n l,
      skipn n (map f l) = map f (skipn n l).
  Proof.
    intro n; induction n as [| n IHn];
      intros [| a l]; simpl in *; f_equal; auto.
  Qed.
End CuttingMap.
