Require Export Coq.Arith.PeanoNat CoqRecon.Util.ListLib.

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

  Local Hint Resolve typ_eq_reflexive : core.
  Local Hint Resolve typ_eq_eq : core.
  
  Lemma typ_eq_iff : forall l r,
      typ_eq l r = true <-> l = r.
  Proof.
    split; intros; subst; auto.
  Qed.

  Lemma typ_eq_reflects : reflects eq typ_eq.
  Proof.
    unfold reflects.
    intros l r; destruct (typ_eq l r) eqn:Hlr;
      constructor; intuition; subst.
    rewrite typ_eq_reflexive in Hlr.
    discriminate.
  Defined.

  Lemma typ_eq_not_eq : forall l r,
      typ_eq l r = false <-> l <> r.
  Proof.
    intros l r.
    pose proof typ_eq_reflects l r as Hlr; inv Hlr;
      intuition.
  Qed.

  Lemma typ_eq_sym : forall l r,
      typ_eq l r = typ_eq r l.
  Proof.
    intros l r.
    pose proof typ_eq_reflects l r as Hlr; inv Hlr; auto.
    apply not_eq_sym in H0.
    rewrite <- typ_eq_not_eq in H0.
    rewrite H0. reflexivity.
  Qed.
End TypEq.

Section TypSize.
  Lemma typ_size_non_zero : forall t,
    typ_size t > 0.
  Proof.
    intro t; induction t; simpl; lia.
  Qed.
End TypSize.
