Require Export Coq.Classes.EquivDec
        Coq.Logic.FunctionalExtensionality
        CoqRecon.Util.Sets CoqRecon.Util.Maybe.

Section Env.
  Context {K V : Set}.

  Definition env : Set := K -> option V.

  Definition empty : env := fun _ => None.
  
  Context {HDK : EqDec K eq}.

  Definition bind (k : K) (v : V) (e : env) : env :=
    fun k' => if equiv_dec k' k then Some v else e k'.

  Definition blind (k : K) (e : env) : env :=
    fun k' => if equiv_dec k' k then None else e k'.
  
  Lemma bind_sound : forall k v e,
      bind k v e k = Some v.
  Proof.
    intros k v e; unfold bind.
    dispatch_eqdec; reflexivity.
  Qed.

  Lemma bind_complete : forall k' k v e,
      k' <> k -> bind k v e k' = e k'.
  Proof.
    intros k' k v e Hk'k; unfold bind.
    dispatch_eqdec; reflexivity.
  Qed.

  Lemma bind_diff_comm : forall x y u v e,
      x <> y ->
      bind x u (bind y v e) = bind y v (bind x u e).
  Proof.
    intros x y u v e Hxy; unfold bind.
    extensionality k.
    repeat dispatch_eqdec; auto.
  Qed.

  Lemma bind_same : forall x u v e,
      bind x u (bind x v e) = bind x u e.
  Proof.
    intros x u v e; unfold bind.
    extensionality k.
    repeat dispatch_eqdec; auto.
  Qed.

  Lemma blind_sound : forall k e, blind k e k = None.
  Proof.
    unfold blind; intros k e.
    dispatch_eqdec; auto.
  Qed.

  Lemma blind_complete : forall k' k e,
      k' <> k -> blind k e k' = e k'.
  Proof.
    unfold blind; intros k' k e Hk'k.
    dispatch_eqdec; auto.
  Qed.

  Lemma blind_comm : forall x y e,
      blind x (blind y e) = blind y (blind x e).
  Proof.
    unfold blind; intros x y e.
    extensionality k.
    repeat dispatch_eqdec; auto.
  Qed.

  Lemma blind_idempotent : forall k e,
      blind k (blind k e) = blind k e.
  Proof.
    unfold blind; intros k e.
    extensionality x.
    repeat dispatch_eqdec; auto.
  Qed.

  Lemma blind_bind_same : forall k v e,
      blind k (bind k v e) = blind k e.
  Proof.
    unfold blind, bind; intros k v e.
    extensionality k'.
    repeat dispatch_eqdec; auto.
  Qed.

  Lemma bind_blind_same : forall k v e,
      bind k v (blind k e) = bind k v e.
  Proof.
    unfold blind, bind; intros k v e.
    extensionality k'.
    repeat dispatch_eqdec; auto.
  Qed.

  Lemma bind_blind_diff : forall x y v e,
      x <> y ->
      bind x v (blind y e) = blind y (bind x v e).
  Proof.
    unfold blind, bind; intros x y v e Hxy.
    extensionality k.
    repeat dispatch_eqdec; auto.
  Qed.

  Definition bound (k : K) (v : V) (e : env) : Prop := e k = Some v.

  Definition mask (e : env) (ks : list K) : env :=
    fun k => if member k ks then None else e k.

  Definition shadow (e1 e2 : env) : env :=
    fun k =>
      match e1 k with
      | Some v => Some v
      | None => e2 k
      end.
  
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

  Definition inclu (e1 e2 : env) : Prop :=
    forall k v, bound k v e1 -> bound k v e2.
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
    dispatch_eqdec; reflexivity.
  Qed.

  Open Scope maybe_scope.
  
  Lemma env_map_map : forall e a,
      env_map e a = e a >>| f.
  Proof.
    intros e a; unfold env_map;
      maybe_simpl; reflexivity.
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
(*Notation "e ∉ ks"
  := (mask e ks)
  (at level 15, left associativity) : env_scope. *)
Notation "eb ≺ ea"
  := (env_compose eb ea)
       (at level 14, left associativity) : env_scope.
