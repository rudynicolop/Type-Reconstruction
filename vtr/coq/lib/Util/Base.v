Require Export Coq.Bool.Bool Coq.Classes.EquivDec.

Ltac inv H := inversion H; subst; clear H.

Ltac eqdec a b :=
  destruct (equiv_dec a b) as [? | ?];
  unfold equiv, complement in *; subst;
  try contradiction; simpl.

Ltac dispatch_eqdec :=
  match goal with
  | |- context [equiv_dec ?a ?b]
    => eqdec a b
  | H: context [equiv_dec ?a ?b] |- _
    => eqdec a b; simpl in *
  end.

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

Lemma Acc_inj : forall {A B : Type} (f : A -> B) (R : B -> B -> Prop) (a : A),
    Acc R (f a) -> Acc (fun a a' => R (f a) (f a')) a.
Proof.
  intros A B f R a HR.
  remember (f a) as fa eqn:Heqfa.
  generalize dependent a.
  induction HR; intros a ?; subst.
  constructor. firstorder.
Qed.

Lemma well_founded_inj : forall {A B : Type} (f : A -> B) (R : B -> B -> Prop),
    well_founded R ->
    well_founded (fun a a' => R (f a) (f a')).
Proof.
  unfold well_founded. intros A B f R.
  intros HR a. eauto using Acc_inj.
Qed.  
