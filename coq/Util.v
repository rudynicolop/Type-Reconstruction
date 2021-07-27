Require Export Coq.Classes.EquivDec
        Coq.Lists.List Coq.Bool.Bool
        Coq.Logic.FunctionalExtensionality.
Export ListNotations.

Ltac inv H := inversion H; subst; clear H.

Lemma contrapositive : forall P Q : Prop,
    (P -> Q) -> ~ Q -> ~ P.
Proof.
  intuition.
Qed.

Lemma nexists_forall_not : forall {A : Type} (P : A -> Prop),
    ~ (exists x, P x) -> forall x, ~ P x.
Proof.
  eauto.
Qed.

Section Curry.
  Context {A B C : Type}.

  Definition curry (f : A * B -> C) (a : A) (b : B) : C := f (a,b).

  Definition uncurry (f : A -> B -> C) '((a,b) : A * B) : C := f a b.

  Local Hint Unfold curry : core.
  Local Hint Unfold uncurry : core.

  Lemma curry_uncurry : forall f ab,
      uncurry (curry f) ab = f ab.
  Proof.
      intros f [a b]; reflexivity.
  Qed.

  Lemma uncurry_curry : forall f a b,
      curry (uncurry f) a b = f a b.
  Proof.
    reflexivity.
  Qed.
End Curry.

Definition reflects
           {A B : Type} (R : A -> B -> Prop) (f: A -> B -> bool) :=
  forall a b, reflect (R a b) (f a b).

Declare Scope set_scope.
Delimit Scope set_scope with set.

Reserved Notation "l ∪ r" (at level 50, left associativity).
Reserved Notation "l ∩ r" (at level 49, left associativity).
Reserved Notation "l ∖ r" (at level 48, left associativity).

Section Sets.
  Context {A : Set}.

  (** [u] is the union of [l] & [r]. *)
  Definition Union (l r u : list A) : Prop :=
    forall a, In a u <-> In a l \/ In a r.

  (** [i] is the intersection of [l] & [r]. *)
  Definition Intersection (l r i : list A) : Prop :=
    forall a, In a i <-> In a l /\ In a r.

  (** [d] is the diff of [l] & [r]. *)
  Definition Difference (l r d : list A) : Prop :=
    forall a, In a d <-> In a l /\ ~ In a r.
  
  Lemma append_Union : forall l r, Union l r (l ++ r).
  Proof.
    unfold Union. auto using in_app_iff.
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
End Sets.

Notation "l ∪ r" := (l ++ r) : set_scope.
Notation "l ∩ r" := (intersect l r) : set_scope.
Notation "l ∖ r" := (difference l r) : set_scope.

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

Declare Scope env_scope.
Delimit Scope env_scope with env.

Notation "'∅'" := empty (at level 0, no associativity) : env_scope.
Notation "k ↦ v ';;' e"
  := (bind k v e)
       (at level 11, right associativity) : env_scope.
Notation "e ∉ ks"
  := (mask e ks)
       (at level 15, left associativity) : env_scope.
