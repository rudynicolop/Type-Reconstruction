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

Section Equiv.
  Context {K V : Set} {HEDK : EqDec K eq}.
  
  Local Hint Unfold eql : core.
  Local Hint Unfold Reflexive : core.

  Notation eqll := (@eql _ V HEDK).

  Lemma eql_reflexive : Reflexive eqll.
  Proof.
    autounfold with *; reflexivity.
  Qed.

  Local Hint Unfold Symmetric : core.

  Lemma eql_symmetric : Symmetric eqll.
  Proof.
    autounfold with *; auto.
  Qed.

  Local Hint Unfold Transitive : core.

  Lemma eql_transitive : Transitive eqll.
  Proof.
    autounfold with *; etransitivity; eauto.
  Qed.

  Local Hint Resolve eql_reflexive : core.
  Local Hint Resolve eql_transitive : core.
  Local Hint Resolve eql_symmetric : core.
  Local Hint Constructors Equivalence : core.

  Global Instance EqlEquiv : Equivalence eqll.
  Proof.
    auto.
  Qed.

  Lemma eql_cons : forall (k : K) (v : V) l l',
      l ≊ l' -> (k,v) :: l ≊ (k,v) :: l'.
  Proof.
    unfold eqll; intros k v l l' H ky;
      simpl; dispatch_eqdec; auto.
  Qed.

  Lemma eql_nil : forall l : list (K * V),
      [] ≊ l -> l = [].
  Proof.
    unfold "≊".
    intro l; destruct l as [| [k v]];
      intro H; try specialize H with k;
        simpl in *; try dispatch_eqdec;
          auto; try discriminate.
  Qed.
End Equiv.

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

  Lemma in_lookup_sublist : forall l (k : K) (v : V),
      In (k,v) l ->
      exists l1 l2, l = l1 ++ l2 /\ lookup k l2 = Some v.
  Proof.
    intro l; induction l as [| [k v] l IHl];
      intros ky vy Hin; simpl in *; try contradiction.
    destruct Hin as [Hkv | Hin]; try inv Hkv.
    - exists [], ((ky,vy) :: l); simpl; dispatch_eqdec; auto.
    - apply IHl in Hin as (l1 & l2 & Hl & Hsome); subst.
      exists ((k,v) :: l1), l2; auto.
  Qed.      
End Env.

Section NoDup.
  Context {K V : Set} {HDK : EqDec K eq}.

  Inductive Once : list (K * V) -> Prop :=
  | once_nil :
      Once []
  | once_cons k v l :
      lookup k l = None ->
      Once l ->
      Once ((k,v) :: l).

  Fixpoint uproot (k : K) (l : list (K * V)) : list (K * V) :=
    match l with
    | []         => []
    | (k',v) :: l => (if k == k' then [] else [(k',v)]) ++ uproot k l
    end.

  Fixpoint collapse (l : list (K * V)) : list (K * V) :=
    match l with
    | []        => []
    | (k,v) :: l => (k,v) :: uproot k (collapse l)
    end.

  Lemma uproot_idempotent : forall l ky,
      uproot ky (uproot ky l) = uproot ky l.
  Proof.
    intro l; induction l as [| [k v] l IHl];
      intro ky; simpl; auto.
    repeat dispatch_eqdec; rewrite IHl; reflexivity.
  Qed.

  Lemma uproot_comm : forall l k1 k2,
      uproot k1 (uproot k2 l) = uproot k2 (uproot k1 l).
  Proof.
    intro l; induction l as [| [k v] l IHl];
      intros k1 k2; simpl; auto.
    repeat dispatch_eqdec; try rewrite IHl; auto.
  Qed.

  Lemma uproot_collapse_comm : forall l ky,
      uproot ky (collapse l) = collapse (uproot ky l).
  Proof.
    intro l; induction l as [| [k v] l IHl];
      intro ky; simpl in *; auto.
    dispatch_eqdec.
    - rewrite uproot_idempotent, IHl; reflexivity.
    - rewrite uproot_comm, IHl; reflexivity.
  Qed.

  Lemma lookup_uproot_same : forall l ky,
      lookup ky (uproot ky l) = None.
  Proof.
    intro l; induction l as [| [k v] l IHl];
      intro ky; simpl; auto.
    repeat dispatch_eqdec; auto.
  Qed.

  Lemma lookup_uproot_diff : forall l k1 k2,
      k1 <> k2 -> lookup k1 (uproot k2 l) = lookup k1 l.
  Proof.
    intro l; induction l as [| [k v] l IHl];
      intros k1 k2 Hk1k2; simpl; auto.
    repeat dispatch_eqdec; auto.
  Qed.
  
  Lemma collapse_eql : forall l, collapse l ≊ l.
  Proof.
    unfold "≊"; intro l;
      induction l as [| [hk hv] l IHl];
      intro k; simpl in *; auto.
    dispatch_eqdec; auto.
    rewrite lookup_uproot_diff by assumption; auto.
  Qed.

  Local Hint Constructors Once : core.
  Local Hint Resolve lookup_uproot_same : core.
  (*Local Hint Resolve lookup_uproot_diff : core.*)
  
  Lemma Once_uproot : forall l,
      Once l -> forall ky, Once (uproot ky l).
  Proof.
    intros l HO; induction HO as [| k v l Hnone HO IHO];
      intro ky; simpl; try dispatch_eqdec; auto.
    constructor; auto.
    rewrite lookup_uproot_diff by auto; assumption.
  Qed.

  Local Hint Resolve Once_uproot : core.
  
  Lemma Once_collapse : forall l, Once (collapse l).
  Proof.
    intro l; induction l as [| [k v] l IHl]; simpl; auto.
  Qed.

  Local Hint Resolve Permutation_sym : core.
  Local Hint Resolve Permutation_map : core.
  Local Hint Resolve Permutation_in : core.
  
  Lemma perm_once : forall l l',
      Permutation l l' -> Once l -> Once l'.
  Proof.
    intros l l' Hp Ho;
      induction Hp as
        [| [k v] l l' Hp IHp
         | [k v] [k' v'] l
         | l l' l'' Hp IHp Hp' IHp'];
      repeat match goal with
             | H: Once (_ :: _) |- _ => inv H
             end; auto.
    - constructor; auto.
      rewrite lookup_none_iff in *.
      firstorder eauto.
    - simpl in *.
      dispatch_eqdec; try discriminate.
      repeat constructor; auto; simpl.
      dispatch_eqdec; auto.
  Qed.

  Local Hint Resolve perm_once : core.
  
  Lemma perm_eql : forall l l',
      Permutation l l' -> Once l -> l ≊ l'.
  Proof.
    unfold eql; intros l l' Hp Ho;
      induction Hp as
        [| [k v] l l' Hp IHp
         | [k v] [k' v'] l
         | l l' l'' Hp IHp Hp' IHp'];
      repeat match goal with
             | H: Once (_ :: _) |- _ => inv H
             end; intro ky; simpl in *; auto.
    - dispatch_eqdec; auto.
    - repeat dispatch_eqdec; try discriminate; auto.
    - intuition; etransitivity; eauto.
  Qed.

  Local Hint Constructors NoDup : core.
  Local Hint Resolve lookup_not_in : core.
  
  Lemma once_nodup : forall l, Once l -> NoDup l.
  Proof.
    intros l Ho; induction Ho; eauto.
  Qed.

  Lemma once_in_lookup : forall l,
      Once l -> forall k v, In (k, v) l -> lookup k l = Some v.
  Proof.
    intros l Ho;
      induction Ho as [| k v l Hnone Ho IHo];
      intros ky vy Hin; simpl in *; try contradiction.
    dispatch_eqdec; destruct Hin as [Hin | Hin];
      try inv Hin; try contradiction; auto.
    apply IHo in Hin. rewrite Hnone in Hin. discriminate.
  Qed.

  Local Hint Resolve lookup_in : core.

  Lemma once_eql_in : forall l l' (k : K) (v : V),
      Once l -> Once l' -> l ≊ l' -> In (k,v) l -> In (k,v) l'.
  Proof.
    unfold eql; intros l l' k v Ho Ho' H Hin.
    apply once_in_lookup in Hin; auto.
    rewrite H in Hin; eauto.
  Qed.

  Local Hint Resolve once_eql_in : core.
  (*Local Hint Resolve eql_symmetric : core.*)

  Lemma once_eql_in_iff : forall l l',
      Once l -> Once l' -> l ≊ l' ->
      forall kv, In kv l <-> In kv l'.
  Proof.
    intros l l' Ho Ho' Heql [k v].
    apply eql_symmetric in Heql as Heql'.
    firstorder eauto.
  Qed.
    
  Local Hint Resolve once_eql_in_iff : core.
  Local Hint Resolve once_nodup : core.
  Local Hint Resolve NoDup_Permutation : core.

  Lemma once_eql_perm : forall l l',
      Once l -> Once l' -> l ≊ l' -> Permutation l l'.
  Proof.
    eauto.
  Qed.

  Local Hint Resolve perm_eql : core.
  Local Hint Resolve once_eql_perm : core.

  Lemma eql_perm_iff : forall l l',
      Once l -> Once l' ->
      l ≊ l' <-> Permutation l l'.
  Proof.
    intuition.
  Qed.
End NoDup.
