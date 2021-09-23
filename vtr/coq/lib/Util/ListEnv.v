Require Export Coq.Classes.EquivDec
        CoqRecon.Util.Sets CoqRecon.Util.Maybe
        CoqRecon.Util.Env.

Open Scope env_scope.
Open Scope maybe_scope.

Section Lookup.
  Context {K V : Set} {HDK : EqDec K eq}.

  Fixpoint lookup (k : K) (l : list (K * V)) : option V :=
    match l with
    | []         => None
    | (k',v) :: l => if k == k' then Some v else lookup k l
    end.

  Fixpoint index_of (k : K) (l : list K) : option nat :=
    match l with
    | []    => None
    | h :: l => if k == h then
                Some 0
              else
                let! n := index_of k l in S n
    end.

  Lemma in_index_of : forall l k,
      In k l -> exists n, index_of k l = Some n.
  Proof.
    intro l; induction l as [| h l IHl];
      intros k Hkl; simpl in *; try contradiction.
    eqdec k h; destruct Hkl as [Hhk | Hkl];
      subst; try contradiction; eauto.
    apply IHl in Hkl as (n & Hn).
    rewrite Hn; maybe_simpl; eauto.
  Qed.

  Lemma index_of_in : forall l k n,
      index_of k l = Some n -> In k l.
  Proof.
    intro l; induction l as [| h l IHl];
      intros k n H; simpl in *; try discriminate.
    dispatch_eqdec; maybe_simpl_hyp H; auto.
    destruct (index_of k l) as [m |] eqn:Hm; inv H;
      firstorder.
  Qed.

  Lemma index_of_nth_error : forall l k n,
      index_of k l = Some n ->
      nth_error l n = Some k.
  Proof.
    intro l; induction l as [| h l IHl];
      intros k n Hio; simpl in *; try discriminate.
    dispatch_eqdec.
    - inv Hio; reflexivity.
    - maybe_simpl_hyp Hio.
      destruct (index_of k l) as [m |] eqn:Hm;
        inv Hio; simpl; auto.
  Qed.

  Lemma nth_error_index_of : forall l n k,
      ~ In k (firstn n l) ->
      nth_error l n = Some k ->
      index_of k l = Some n.
  Proof.
    intro l; induction l as [| h l IHl];
      intros [| n] k Hnf Hnth; simpl in *;
        try discriminate.
    - inv Hnth; dispatch_eqdec; reflexivity.
    - apply Decidable.not_or in Hnf as [Hhk Hnf].
      dispatch_eqdec; maybe_simpl.
      erewrite IHl by eauto; reflexivity.
  Qed.

  Lemma index_of_not_in_iff : forall l k,
      index_of k l = None <-> ~ In k l.
  Proof.
    intro l; induction l as [| h l IHl];
      intros k; split; intro H; simpl in *; auto.
    - intros [Hhk | Hkl]; subst; dispatch_eqdec;
        try discriminate; maybe_simpl_hyp H.
      destruct (index_of k l) as [n |] eqn:Hn;
        try discriminate; firstorder.
    - apply Decidable.not_or in H as [Hhk Hkl].
      dispatch_eqdec; maybe_simpl.
      rewrite <- IHl in Hkl; rewrite Hkl; reflexivity.
  Qed.
  
  Definition lookup' (k : K) (l : list (K * V)) : option V :=
    let* n := index_of k (map fst l) in nth_error (map snd l) n.

  Lemma lookup_lookup' : forall l (k : K),
      lookup k l = lookup' k l.
  Proof.
    unfold lookup'.
    intro l; induction l as [| [h v] l IHl];
      intro k; maybe_simpl; auto.
    specialize IHl with k.
    dispatch_eqdec; auto.
    destruct (index_of k (map fst l))
      as [n |] eqn:Heqn; maybe_simpl_hyp IHl;
      maybe_simpl; auto.
  Qed.
  
  Definition to_env : list (K * V) -> @env K V :=
    fold_right (uncurry bind) ∅.

  Definition combine_to_env (ks : list K) (vs : list V) : @env K V :=
    to_env (combine ks vs).
  
  Definition eql (l1 l2 : list (K * V)) : Prop :=
    forall k, lookup k l1 = lookup k l2.

  Definition env_eq (l : list (K * V)) (e : @env K V) : Prop :=
    forall k, lookup k l = e k.
End Lookup.

Notation "l1 ≊ l2"
  := (eql l1 l2)
       (at level 70, no associativity) : type_scope.

Notation "l ⩰ e"
  := (env_eq l e)
       (at level 70, no associativity) : type_scope.

Notation "'~[' ks ⟼  vs ']~'"
  := (combine_to_env ks vs)
       (at level 4, no associativity) : env_scope.

Section Map.
  Context {A B : Set}.
  Variable (f : A -> B).

  Lemma nth_error_map : forall l n,
      nth_error (map f l) n = omap f (nth_error l n).
  Proof.
    intro l; induction l as [| a l IHl];
      intros [| n]; maybe_simpl; eauto.
  Qed.

  Context {HAED : EqDec A eq} {HBED : EqDec B eq}.
  Hypothesis f_inj : forall a1 a2, f a1 = f a2 -> a1 = a2.
  
  Lemma index_of_map : forall l a,
      index_of (f a) (map f l) = index_of a l.
  Proof.
    intro l; induction l as [| h l IHl];
      intro a; simpl in *; auto.
    repeat dispatch_eqdec;
      maybe_simpl; firstorder.
    rewrite IHl; reflexivity.
  Qed.

  Lemma index_of_map_eq : forall l a b,
      b = f a -> index_of b (map f l) = index_of a l.
  Proof.
    intros l a b Hbfa; subst.
    auto using index_of_map.
  Qed.
End Map.

Section Env.
  Context {K V : Set} {HDK : EqDec K eq}.
  
  Lemma cons_env_sound : forall (k : K) (v : V) (l : list (K * V)),
      lookup k ((k,v) :: l) = Some v.
  Proof.
    intros k v l; simpl.
    dispatch_eqdec; auto.
  Qed.

  Lemma cons_env_complete : forall (x k : K) (v : V) (l : list (K * V)),
      x <> k -> lookup x ((k,v) :: l) = lookup x l.
  Proof.
    intros x k v l Hxk; simpl.
    dispatch_eqdec; auto.
  Qed.

  Local Hint Unfold eql : core.
  
  Lemma cons_env_same : forall (k : K) (v v' : V) (l : list (K * V)),
      (k,v) :: (k,v') :: l ≊ (k,v) :: l.
  Proof.
    intros k v v' l k'; simpl;
      repeat dispatch_eqdec; auto.
  Qed.

  Lemma cons_env_diff_comm : forall (x y : K) (u v : V) (l : list (K * V)),
      x <> y -> (x,u) :: (y,v) :: l ≊ (y,v) :: (x,u) :: l.
  Proof.
    intros x y u v l Hxy k; simpl;
      repeat dispatch_eqdec; auto.
  Qed.
  
  Lemma to_env_sound : forall l : list (K * V),
      l ⩰ to_env l.
  Proof.
    unfold to_env, "⩰", "∅".
    intro l; induction l as [| [k v] l IHl];
      intro k'; simpl; auto.
    unfold bind at 1.
    dispatch_eqdec; auto.
  Qed.
  
  Lemma to_env_eql : forall l l' : list (K * V),
      l ≊ l' -> to_env l = to_env l'.
  Proof.
    unfold "≊", to_env, "∅".
    intro l; induction l as [| [k v] l IHl];
      intros [| [k' v'] l'] Heql;
      extensionality x;
      specialize Heql with x as Heql';
      simpl in *; try unfold bind at 1;
        repeat dispatch_eqdec; auto.
    - rewrite Heql' at 1. apply to_env_sound.
    - symmetry. rewrite <- Heql' at 1.
      apply to_env_sound.
    - rewrite bind_sound. assumption.
    - rewrite bind_complete by assumption.
      rewrite Heql'. apply to_env_sound.
    - rewrite bind_sound. symmetry.
      rewrite <- Heql'. apply to_env_sound.
    - rewrite bind_complete by assumption.
      apply equal_f; apply IHl.
      intro y; specialize Heql with y.
      repeat dispatch_eqdec; auto.
  Abort.

  Lemma combine_to_env_lookup : forall ks (vs : list V) k,
      ~[ ks ⟼  vs ]~ k = lookup k (combine ks vs).
  Proof.
    intros ks vs k. unfold combine_to_env.
    symmetry. apply to_env_sound.
  Qed.

  Lemma lookup_in : forall l (k : K) (v : V),
      lookup k l = Some v -> In (k,v) l.
  Proof.
    intro l; induction l as [| [k' v'] l IHl];
      intros k v; simpl; intros H;
        try discriminate; dispatch_eqdec; firstorder; inv H; auto.
  Qed.

  Lemma lookup_not_in : forall l (k : K),
      lookup k l = None -> forall v : V, ~ In (k,v) l.
  Proof.
    intro l; induction l as [| [k' v'] l IHl];
      intros k H v; simpl in *; auto;
        dispatch_eqdec; inv H; intros [Hkv | Hkv];
          try inv Hkv; try contradiction; firstorder.
  Qed.

  Lemma lookup_not_in_domain : forall (l : list (K * V)) k,
      lookup k l = None -> ~ In k (map fst l).
  Proof.
    intro l; induction l as [| [k v] l IHl];
      intros ky Hnone Hin; simpl in *; auto.
    dispatch_eqdec; try discriminate; firstorder.
  Qed.

  Lemma not_in_domain_lookup : forall (l : list (K * V)) k,
      ~ In k (map fst l) -> lookup k l = None.
  Proof.
    intros l; induction l as [| [k v] l IHl];
      intros ky Hnin; simpl in *; auto.
    apply Decidable.not_or in Hnin as [Hkky Hnin].
    dispatch_eqdec; auto.
  Qed.

  Local Hint Resolve lookup_not_in_domain : core.
  Local Hint Resolve not_in_domain_lookup : core.

  Lemma lookup_none_iff : forall (l : list (K * V)) k,
      lookup k l = None <-> ~ In k (map fst l).
  Proof.
    firstorder.
  Qed.
  
  Lemma lookup_in_domain : forall l (k : K) (v : V),
      lookup k l = Some v -> In k (map fst l).
  Proof.
    intros l k v Hkl.
    rewrite lookup_lookup' in Hkl.
    unfold lookup' in Hkl; maybe_simpl_hyp Hkl.
    destruct (index_of k (map fst l))
      as [n |] eqn:Heqn; try discriminate.
    eauto using index_of_in.
  Qed.

  Lemma lookup_in_image : forall l (k : K) (v : V),
      lookup k l = Some v -> In v (map snd l).
  Proof.
    intros l k v Hklv.
    rewrite lookup_lookup' in Hklv.
    unfold lookup' in Hklv; maybe_simpl_hyp Hklv.
    destruct (index_of k (map fst l))
      as [n |] eqn:Heqn; try discriminate.
    eauto using nth_error_In.
  Qed.

  Lemma in_domain_lookup : forall l (k : K),
      In k (map fst l) -> exists v : V, lookup k l = Some v.
  Proof.
    intros l k Hin.
    rewrite lookup_lookup'; unfold lookup'.
    apply in_index_of in Hin as Hidx.
    destruct Hidx as [m Hm]; rewrite Hm; maybe_simpl.
    apply index_of_nth_error in Hm.
    rewrite nth_error_map in Hm; maybe_simpl_hyp Hm.
    rewrite nth_error_map; maybe_simpl.
    destruct (nth_error l m) as [[k' v'] |] eqn:Hnth;
      simpl in *; try discriminate; eauto.
  Qed.
  
  Lemma in_lookup_nodup : forall l (k : K) (v : V),
      NoDup (map fst l) -> In (k, v) l -> lookup k l = Some v.
  Proof.
    intro l; induction l as [| [k' v'] l IHl];
      intros k v Hnd Hin; simpl in *; inv Hnd; try contradiction.
    dispatch_eqdec; destruct Hin as [Hin | Hin];
      try inv Hin; auto; try contradiction. exfalso.
    destruct (combine_ex l) as (ks & vs & Hcmb & Hlen); subst.
    apply in_combine_l in Hin.
    rewrite combine_map_fst in H1.
    rewrite <- Hlen in H1.
    rewrite Min.min_idempotent in H1.
    rewrite firstn_all in H1.
    contradiction.
  Qed.

  Lemma combine_to_env_some : forall ks vs (k : K) (v : V),
      ~[ ks ⟼  vs ]~ k = Some v ->
      exists ks1 ks2 vs1 vs2,
        combine ks vs = combine ks1 vs1 ++ (k,v) :: combine ks2 vs2
        /\ ~ In k ks1.
  Proof.
    intros ks vs k v.
    rewrite combine_to_env_lookup.
    generalize dependent v;
      generalize dependent k;
      generalize dependent vs.
    induction ks as [| k ks IHks];
      intros [| v vs] kk vv Hkv; simpl in *; try discriminate.
    dispatch_eqdec.
    - inv Hkv.
      exists [], ks, [], vs; intuition.
    - apply IHks in Hkv as (ks1 & ks2 & vs1 & vs2 & Hcmb & Hks1).
      exists (k :: ks1), ks2, (v :: vs1), vs2.
      rewrite Hcmb. firstorder.
  Qed.

  Lemma in_image_lookup : forall l (v : V),
      NoDup (map fst l) ->
      In v (map snd l) ->
      exists (k : K), lookup k l = Some v.
  Proof.
    intro l; induction l as [| [hk hv] l IHl];
      intros v Hnd Hin; inv Hnd; simpl in *; try contradiction.
    destruct Hin as [? | Hin]; subst.
    - exists hk; dispatch_eqdec; reflexivity.
    - pose proof IHl _ H2 Hin as [k' IH]; clear IHl.
      exists k'; dispatch_eqdec; auto.
      apply lookup_in_domain in IH. contradiction.
  Qed.
End Env.
