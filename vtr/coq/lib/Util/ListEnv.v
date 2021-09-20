Require Export Coq.Classes.EquivDec
        CoqRecon.Util.Sets CoqRecon.Util.Maybe
        CoqRecon.Util.Env.

Open Scope env_scope.

Section Lookup.
  Context {K V : Set} {HDK : EqDec K eq}.

  Fixpoint lookup (k : K) (l : list (K * V)) : option V :=
    match l with
    | []         => None
    | (k',v) :: l => if k == k' then Some v else lookup k l
    end.
  
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
End Env.
