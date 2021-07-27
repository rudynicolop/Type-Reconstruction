Require Export Coq.Classes.EquivDec Coq.Lists.List Coq.Bool.Bool.
Export ListNotations.

Ltac inv H := inversion H; subst; clear H.

Definition reflects
           {A B : Type} (R : A -> B -> Prop) (f: A -> B -> bool) :=
  forall a b, reflect (R a b) (f a b).

Section Env.
  Context {K V : Set}.

  Definition env : Set := K -> option V.

  Definition empty : env := fun _ => None.
  
  Context {HDK : EqDec K eq}.

  Definition bind (k : K) (v : V) (e : env) : env :=
    fun k' => if equiv_dec k' k then Some v else e k'.

  Definition find (k : K) (e : env) : option V := e k.

  Definition bound (k : K) (v : V) (e : env) : Prop := e k = Some v.
End Env.

Declare Scope env_scope.
Delimit Scope env_scope with env.

Notation "'∅'" := empty (at level 0, no associativity) : env_scope.
Notation "k ↦ v ';;' e"
  := (bind k v e)
       (at level 11, right associativity) : env_scope.
(*Notation "k ↦ v ∈ e"
  := (bound k v e) (at level 10, no associativity) : env_scope.*)

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
