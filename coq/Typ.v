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

Coercion TVar : nat >-> typ.
Notation "t1 → t2"
  := (TArrow t1 t2)
       (at level 30, right associativity) : typ_scope.

Open Scope typ_scope.

Fixpoint typ_eq (l r : typ) : bool :=
  match l, r with
  | TBool, TBool | TNat, TNat => true
  | TVar T1, TVar T2 => T1 =? T2
  | l → l', r → r'
    => typ_eq l r && typ_eq l' r'
  | _, _ => false
  end.

Fixpoint tvars (t : typ) : list nat :=
  match t with
  | TBool | TNat => []
  | TVar T => [T]
  | t → t' => tvars t ++ tvars t'
  end.

Fixpoint typ_size (t : typ) : nat :=
  match t with
  | TBool | TNat | TVar _ => 1
  | t → t' => 1 + typ_size t + typ_size t'
  end.

Definition typ_size_vars (t : typ) : nat * nat :=
  (length (uniques (tvars t)), typ_size t).

Definition Ctvars : list (typ * typ) -> list nat :=
  fold_right (fun '(l,r) acc => tvars l ++ tvars r ++ acc) [].

Definition C_size : list (typ * typ) -> nat :=
  fold_right (fun '(l,r) acc => typ_size l + typ_size r + acc) 0.

Definition C_size_vars (C : list (typ * typ)) : nat * nat :=
  (length (uniques (Ctvars C)), C_size C).
    
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
End TypSize.

Definition tenv : Set := @env nat typ.

Reserved Notation "s † t" (at level 20, right associativity).

Fixpoint tsub (σ : tenv) (t : typ) {struct t} : typ :=
  match t with
  | TBool => TBool
  | TNat => TNat
  | t → t' => σ † t → σ † t'
  | TVar T => match σ T with
             | Some τ => τ
             | None => T
             end
  end
where "σ † t" := (tsub σ t) : typ_scope.

Definition Ctsub (s : tenv) : list (typ * typ) -> list (typ * typ) :=
  map (fun '(l,r) => (s † l, s † r)).

Definition tsub_compose (s1 s2 : tenv) : tenv :=
  env_map (tsub s1) s2.

Notation "s1 ‡ s2"
  := (tsub_compose s1 s2)
       (at level 21, left associativity) : env_scope.

Definition satisfy σ τ1 τ2 : Prop := σ † τ1 = σ † τ2.

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
  Lemma tsub_empty : forall t, ∅%env † t = t.
  Proof.
    intro t; induction t; simpl in *; auto.
    rewrite IHt1. rewrite IHt2. reflexivity.
  Qed.

  Lemma tsub_not_in_tvars : forall t t' T s,
      ~ In T (tvars t) ->
      (T ↦ t';; s)%env † t = s † t.
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

  Open Scope set_scope.
  
  Lemma tsub_length_count_tvars : forall τ t T,
      T ∉ tvars t ->
      length (tvars ((T ↦ t;; ∅)%env † τ)) =
      count T (tvars τ) * length (tvars t) +
      length (tvars τ) - count T (tvars τ).
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | X];
      intros t T HTt; simpl in *; auto.
    - apply IHt1 in HTt as IH1; clear IHt1;
        apply IHt2 in HTt as IH2; clear IHt2.
      repeat rewrite app_length. rewrite IH1, IH2.
      repeat rewrite count_app.
      pose proof count_length_le (tvars t1) T as HCL1.
      pose proof count_length_le (tvars t2) T as HCL2. lia.
    - unfold bind. dispatch_eqdec; try lia.
  Qed.

  Lemma tsub_length_uniques_tvars : forall τ t T,
      T ∉ tvars t -> T ∈ tvars τ ->
      length (uniques (tvars ((T ↦ t;; ∅)%env † τ))) =
      length (uniques (tvars τ ∪ tvars t)) - 1.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2| x];
      intros t T HTt HTτ; simpl in *; try contradiction.
    - rewrite in_app_iff in HTτ.
      pose proof In_member_reflects T (tvars t1) as HTt1.
      pose proof In_member_reflects T (tvars t2) as HTt2.
      inv HTt1; inv HTt2; destruct HTτ as [HTt1 | HTt2];
        try contradiction.
      + pose proof IHt1 _ _ HTt HTt1 as IH1; clear IHt1.
        pose proof IHt2 _ _ HTt H2   as IH2; clear IHt2.
        repeat rewrite uniques_app_diff in *.
        repeat rewrite app_length in *.
        Search (length (_ ∖ _)).
        rewrite IH1.
        Check difference_app_r_assoc.
        rewrite <- difference_app_r_assoc.
  Abort.
End TSub.
