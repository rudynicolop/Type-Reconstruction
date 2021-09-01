Require Export Coq.micromega.Lia CoqRecon.Base.
Require Import Coq.Relations.Relation_Operators
        Coq.Wellfounded.Lexicographic_Product
        Coq.Logic.FunctionalExtensionality Wf_nat.

Reserved Notation "x ⊏ y" (at level 70, no associativity).
Reserved Notation "x ≤ y" (at level 70, no associativity).

Section Prod.
  Context {A B : Type}.
  
  Definition nondep_prod '((a,b) : A * B) : {_ : A & B} := existT _ a b.
  
  Section WF.
    Variable R : A * B -> A * B -> Prop.
    Variable S : {_ : A & B} -> {_ : A & B} -> Prop.

    Hypothesis HRS : forall a b a' b',
        R (a,b) (a',b') <-> S (existT _ a b) (existT _ a' b').

    Lemma prod_acc : forall a b,
        Acc R (a,b) <-> Acc S (existT _ a b).
    Proof.
      intros a b; split; intros H.
      - remember (a, b) as ab;
          generalize dependent b;
          generalize dependent a.
        induction H as [[a' b'] _ IH];
          intros a b Heq; inv Heq; subst.
        constructor. intros [a' b'] HS.
        rewrite <- HRS in HS. firstorder.
      - remember (existT _ a b) as ab;
          generalize dependent b;
          generalize dependent a.
        induction H as [[a' b'] _ IH];
          intros a b Heq; inv Heq; subst.
        constructor. intros [a' b'] HR.
        rewrite HRS in HR. firstorder.
    Qed.

    Local Hint Resolve prod_acc : core.

    Lemma prod_wf :
      well_founded R <->
      well_founded S.
    Proof.
      unfold well_founded. split; intros H [a b].
      - rewrite <- prod_acc; auto.
      - rewrite prod_acc; auto.
    Qed.
  End WF.
End Prod.
        
Definition lex_prod {A B : Type}
           (leA : A -> A -> Prop) (leB : B -> B -> Prop)
           (p p' : A * B) : Prop :=
  lexprod A (fun _ => B) leA (fun _ => leB) (nondep_prod p) (nondep_prod p').

Definition le_pair : nat * nat -> nat * nat -> Prop := lex_prod lt le.

Notation "p1 ≤ p2" := (le_pair p1 p2) : type_scope.

Definition lt_pair_le
           '((m,n) : nat * nat) '((m',n') : nat * nat) : Prop := (m, S n) ≤ (m', n').

Definition lt_pair : nat * nat -> nat * nat -> Prop := lex_prod lt lt.

Notation "p1 ⊏ p2" := (lt_pair p1 p2) : type_scope.

Lemma lt_pair_spec : forall p p' : nat * nat,
    p ⊏ p' <-> lt_pair_le p p'.
Proof.
  intros [m n] [m' n']; unfold "⊏", lt_pair_le, "≤", lex_prod.
  split; intros H; inv H.
  - left; assumption.
  - right; assumption.
  - left; assumption.
  - right; assumption.
Qed.

Local Hint Resolve lt_wf : core.

Theorem wf_lt_pair : well_founded lt_pair.
Proof.
  rewrite prod_wf with
      (S := lexprod nat (fun _ => nat) lt (fun _ => lt))
    by intuition.
  apply wf_lexprod; auto.
Qed.
