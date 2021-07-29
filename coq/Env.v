Require Export Coq.Classes.EquivDec
        Coq.Logic.FunctionalExtensionality
        CoqRecon.Sets.

Section Env.
  Context {K V : Set}.

  Definition env : Set := K -> option V.

  Definition empty : env := fun _ => None.
  
  Context {HDK : EqDec K eq}.

  Definition bind (k : K) (v : V) (e : env) : env :=
    fun k' => if equiv_dec k' k then Some v else e k'.

  Lemma bind_sound : forall k v e,
      (bind k v e) k = Some v.
  Proof.
    intros k v e; unfold bind.
    destruct (equiv_dec k k) as [Hk | Hk];
      unfold equiv in *; try contradiction.
    reflexivity.
  Qed.

  Lemma bind_complete : forall k' k v e,
      k' <> k -> (bind k v e) k' = e k'.
  Proof.
    intros k' k v e Hk'k; unfold bind.
    destruct (equiv_dec k' k) as [Hk | Hk];
      unfold equiv in *; try contradiction.
    reflexivity.
  Qed.

  Definition find (k : K) (e : env) : option V := e k.

  Definition bound (k : K) (v : V) (e : env) : Prop := e k = Some v.

  Definition mask (e : env) (ks : list K) : env :=
    fun k => if member k ks then None else e k.

  Definition dom (e : env) (d : list K) : Prop :=
    forall k, In k d <-> exists v, e k = Some v.

  Lemma env_binds : forall (k : K) (e : env),
      e k = None \/ exists v, e k = Some v.
  Proof.
    intros k e.
    destruct (e k) eqn:Heq; eauto.
  Qed.
  
  Lemma dom_nil : forall e, dom e [] -> e = empty.
  Proof.
    unfold dom. intros e H.
    extensionality k. unfold empty.
    specialize H with k.
    destruct (env_binds k e) as [He | He]; auto.
    apply H in He. inv He.
  Qed.

  Lemma not_in_dom : forall k d e,
      dom e d -> ~ In k d -> e k = None.
  Proof.
    intros k d e Hdom HIn; unfold dom in *.
    specialize Hdom with k.
    destruct Hdom as [_ Hd].
    pose proof contrapositive _ _ Hd as H.
    apply H in HIn.
    pose proof nexists_forall_not _ HIn as HE.
    destruct (env_binds k e) as [Hk | [v Hk]]; auto.
    apply HE in Hk. contradiction.
  Qed.

  Definition range (e : env) (r : list V) : Prop :=
    forall v, In v r <-> exists k, e k = Some v.
End Env.

Section EnvMap.
  Context {A B C : Set}.
  Variable (f : B -> C).
  Context {HDK : EqDec A eq}.

  Definition env_map (e : @env A B) : @env A C :=
    fun a => match e a with
          | Some b => Some (f b)
          | None => None
          end.

  Lemma env_map_bind : forall a b e,
      bind a (f b) (env_map e) = env_map (bind a b e).
  Proof.
    intros a b e; extensionality k.
    unfold bind, env_map.
    destruct (equiv_dec k a) as [Hka | Hka];
      unfold equiv in *; subst; reflexivity.
  Qed.
End EnvMap.

Section ComposeEnv.
  Context {A B C : Set}.

  Definition env_compose (eb : @env B C) (ea : @env A B) : @env A C :=
    fun a => match ea a with
          | Some b => eb b
          | None => None
          end.
End ComposeEnv.

Declare Scope env_scope.
Delimit Scope env_scope with env.

Notation "'∅'" := empty (at level 0, no associativity) : env_scope.
Notation "k ↦ v ';;' e"
  := (bind k v e)
       (at level 11, right associativity) : env_scope.
Notation "e ∉ ks"
  := (mask e ks)
       (at level 15, left associativity) : env_scope.
Notation "eb ≺ ea"
  := (env_compose eb ea)
       (at level 14, left associativity) : env_scope.
