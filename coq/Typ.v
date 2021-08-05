Require Export Coq.Strings.String
        CoqRecon.Env
        Coq.micromega.Lia
        Coq.Arith.PeanoNat.

Inductive typ : Set :=
| TBool
| TNat
| TArrow : typ -> typ -> typ
| TVar : nat -> typ.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Notation "t1 → t2"
  := (TArrow t1 t2)
       (at level 30, right associativity) : typ_scope.

Fixpoint typ_eq (l r : typ) : bool :=
  match l, r with
  | TBool, TBool | TNat, TNat => true
  | TVar T1, TVar T2 => T1 =? T2
  | (l → l')%typ, (r → r')%typ
    => typ_eq l r && typ_eq l' r'
  | _, _ => false
  end.

Fixpoint tvars (t : typ) : list nat :=
  match t with
  | TBool | TNat => []
  | TVar T => [T]
  | (t → t')%typ => tvars t ++ tvars t'
  end.

Fixpoint typ_size (t : typ) : nat :=
  match t with
  | TBool | TNat | TVar _ => 1
  | (t → t')%typ => 1 + typ_size t + typ_size t'
  end.

(** Want an ordering such that,
    let m be # of unique type vars,
    & n be the size,
    (m,n) < (m',n') iff
    m < m' \/ m = m' /\ n < n'.

    let (m,n) = n % m.

    Is (9,5) < (8,6)?

    5 % 9 = 5
    6 % 8 = 6.

    No...
    *)

Definition typ_size_vars (t : typ) : nat :=
  let i := length (remove_dups (tvars t)) in
  let j := typ_size t in
  i * (1 + i) + j.

Definition Ctvars : list (typ * typ) -> list nat :=
  fold_right (fun '(l,r) acc => tvars l ++ tvars r ++ acc) [].

Definition C_size : list (typ * typ) -> nat :=
  fold_right (fun '(l,r) acc => typ_size l + typ_size r + acc) 0.

Definition C_size_vars (C : list (typ * typ)) : nat :=
  let i := length (remove_dups (Ctvars C)) in
  let j := C_size C in
  i * (1 + i) + j.
    
Section TypEq.
  Lemma typ_eq_reflexive : forall t, typ_eq t t = true.
  Proof.
    Local Hint Resolve andb_true_intro : core.
    Local Hint Resolve Nat.eqb_refl : core.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      simpl; try reflexivity; auto.
  Qed.
  
  Lemma typ_eq_eq : forall l r,
      typ_eq l r = true -> l = r.
  Proof.
    Hint Rewrite andb_true_iff : core.
    Hint Rewrite Nat.eqb_eq : core.
    intro l; induction l as [| | l IHl l' IHl' | L];
      intros [| | r r' | R] H; simpl in *;
        try discriminate; try reflexivity;
          autorewrite with core in *; f_equal; intuition.
  Qed.
End TypEq.

Section TypSize.
  Lemma typ_size_non_zero : forall t,
    typ_size t > 0.
  Proof.
    intro t; induction t; simpl; lia.
  Qed.

  (*Lemma typ_size_arrow_left : forall l r,
      typ_size (l → r)%typ*)  
  
  Lemma typ_size_vars_non_zero : forall t,
      typ_size_vars t > 0.
  Proof.
    intros t; unfold typ_size_vars.
    pose proof typ_size_non_zero t; lia.
  Qed.
End TypSize.

Definition tenv : Set := @env nat typ.

Reserved Notation "s † t" (at level 20, right associativity).

Fixpoint tsub (σ : tenv) (t : typ) {struct t} : typ :=
  match t with
  | TBool => TBool
  | TNat => TNat
  | (t → t')%typ => (σ † t → σ † t')%typ
  | TVar T => match σ T with
             | Some τ => τ
             | None => TVar T
             end
  end
where "σ † t" := (tsub σ t) : typ_scope.

Definition Ctsub (s : tenv) : list (typ * typ) -> list (typ * typ) :=
  map (fun '(l,r) => (s † l, s † r)%typ).

Definition tsub_compose (s1 s2 : tenv) : tenv :=
  env_map (tsub s1) s2.

Notation "s1 ‡ s2"
  := (tsub_compose s1 s2)
       (at level 21, left associativity) : env_scope.

Definition satisfy σ τ1 τ2 : Prop := (σ † τ1 = σ † τ2)%typ.

Section Satisfy.
  Lemma satisfy_reflexive : forall σ, Reflexive (satisfy σ).
  Proof.
    unfold Reflexive, satisfy; reflexivity.
  Qed.
  
  Lemma satisfy_symmetric : forall σ, Symmetric (satisfy σ).
  Proof.
    unfold Symmetric, satisfy; auto.
  Qed.
  
  Lemma satisfy_transitive : forall σ, Transitive (satisfy σ).
  Proof.
    unfold Transitive, satisfy; intros; etransitivity; eauto.
  Qed.
End Satisfy.

Definition gamma : Set := @env string typ.

Notation "s × g" := (env_map (tsub s) g)
                      (at level 25, right associativity) : env_scope.

Section TSub.
  Lemma tsub_empty : forall t, (∅%env † t)%typ = t.
  Proof.
    intro t; induction t; simpl in *; auto.
    rewrite IHt1. rewrite IHt2. reflexivity.
  Qed.

  Lemma tsub_not_in_tvars : forall t t' T s,
      ~ In T (tvars t) ->
      ((T ↦ t';; s)%env † t = s † t)%typ.
  Proof.
    intro t;
      induction t as [| | t1 IHt1 t2 IHt2 | X];
      intros t' T s HIn; simpl in *; auto.
    - rewrite in_app_iff in HIn.
      apply Decidable.not_or in HIn as [Ht1 Ht2].
      rewrite IHt1,IHt2 by eauto. reflexivity.
    - apply Decidable.not_or in HIn as [Ht _].
      rewrite bind_complete by intuition. reflexivity.
  Qed.

  Lemma Ctsub_empty : forall C,
      Ctsub ∅%env C = C.
  Proof.
    intro C; induction C as [| [l r] C IHC]; simpl; auto.
    repeat rewrite tsub_empty. rewrite IHC. reflexivity.
  Qed.

  Lemma Ctsub_not_in_tvars : forall C T t s,
      ~ In T (Ctvars C) ->
      Ctsub (T ↦ t;; s)%env C = Ctsub s C.
  Proof.
    intro C; induction C as [| [l r] C IHC];
      intros T t s HT; simpl in *; auto.
    repeat rewrite in_app_iff in HT.
    apply Decidable.not_or in HT as [HT1 HT2].
    apply Decidable.not_or in HT2 as [HT2 HT3].
    repeat rewrite tsub_not_in_tvars by auto.
    rewrite IHC by auto. reflexivity.
  Qed.
  
  Lemma tsub_gamma_empty : forall g : gamma, (∅ × g = g)%env.
  Proof.
    intros g. extensionality n.
    unfold env_map.
    destruct (g n) eqn:Heq; auto.
    rewrite tsub_empty. reflexivity.
  Qed.

  Lemma tsub_gamma_not_in_tvars : forall T t (g : gamma) (s : tenv),
      (forall x tx, g x = Some tx -> ~ In T (tvars tx)) ->
      ((T ↦ t;; s) × g = s × g)%env.
  Proof.
    intros T t g s Hg.
    extensionality y.
    repeat rewrite env_map_map.
    maybe_simpl.
    destruct (g y) as [ty |] eqn:Hgy; auto.
    apply Hg in Hgy. f_equal.
    apply tsub_not_in_tvars; auto.
  Qed.
  
  Lemma tsub_single_size : forall τ t X,
      ~ In X (tvars t) ->
      let s := (X ↦ t;; ∅)%env in
      typ_size (s † τ)%typ <= S (typ_size t + typ_size τ).
  Proof.
    intros τ t X HIn s; subst s.
      generalize dependent X;
      generalize dependent t.
      induction τ as [| | t1 IHt1 t2 IHt2 | T];
        intros t X HIn; simpl; try lia.
    - admit.
    - destruct (equiv_dec T X) as [HTX | HTX];
        unfold equiv, complement in *; subst.
      + rewrite bind_sound. lia.
      + rewrite bind_complete by assumption.
        simpl. lia.
  Abort.

  Lemma tsub_unique_vars : forall τ t X,
      ~ In X (tvars t) ->
      let s := (X ↦ t;; ∅)%env in
      length (remove_dups (tvars (s † τ)%typ))
      <= S (length (remove_dups (tvars τ ++ tvars t))).
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros t X HIn s; subst s; simpl; try lia.
    - pose proof IHt1 t X HIn as IH1; clear IHt1.
      pose proof IHt2 t X HIn as IH2; clear IHt2.
      simpl in *. admit.
    - destruct (equiv_dec T X) as [HXT | HXT];
        unfold equiv, complement in *; subst; simpl in *.
      + rewrite bind_sound.
        rewrite app_length; lia.
      + rewrite bind_complete by assumption.
        simpl; lia.        
  Abort.
End TSub.
