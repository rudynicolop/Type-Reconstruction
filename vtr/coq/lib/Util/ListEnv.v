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

Notation "'[[' ks ⟼  vs ']]'"
  := (combine_to_env ks vs)
       (at level 10, no associativity) : env_scope.

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
End Env.
