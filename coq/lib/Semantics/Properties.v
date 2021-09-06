Require Export CoqRecon.Semantics.DeclTyping CoqRecon.Semantics.Reduce.

Section Canon.
  Variable v : term.

  Hypothesis Hv : value v.
  
  Lemma canon_abs : forall t t',
      ∅ ⊨ v ∴ t → t' -> exists x e, v = λ x ⇒ e.
  Proof.
    intros t t' Ht; inv Hv; inv Ht; eauto.
  Qed.

  Lemma canon_nat : ∅ ⊨ v ∴ TNat -> exists n : nat, v = n.
  Proof.
    intros Ht; inv Hv; inv Ht; eauto.
  Qed.

  Lemma canon_bool : ∅ ⊨ v ∴ TBool -> exists b : bool, v = b.
  Proof.
    intros Ht; inv Hv; inv Ht; eauto.
  Qed.
End Canon.

Section Progress.
  Local Hint Constructors value : core.
  Local Hint Constructors typing : core.

  Local Hint Extern 0 =>
  match goal with
  | |- context [if ?b then _ else _] =>
    destruct b eqn:?; simpl
  end : core.

  Theorem prog : forall e t,
      ∅ ⊨ e ∴ t -> value e \/ exists e', rd e = Some e'.
  Proof.
    intro e;
      induction e as
        [ x
        | x e IHe
        | e1 IHe1 e2 IHe2
        | n | b
        | e1 IHe1 e2 IHe2 e3 IHe3
        | o e1 IHe1 e2 IHe2
        | x e1 IHe1 e2 IHe2 ];
      intros t Ht; inv Ht; simpl;
        repeat match goal with
               | H: op_typs _ _ _ |- _ => inv H
               | IH: (forall t, ?g ⊨ ?e ∴ t -> _), H : ?g ⊨ ?e ∴ ?t
                 |- _ => pose proof IH t H as [? | [? ?]]; clear IH
               | H: ∅ ⊨ ?v ∴ _ → _, Hv: value ?v
                 |- _ => pose proof canon_abs v Hv _ _ H as (? & ? & ?);
                         clear Hv; subst; simpl
               | H: ∅ ⊨ ?v ∴ TNat, Hv: value ?v
                 |- _ => pose proof canon_nat v Hv H as (? & ?);
                         clear Hv; subst; simpl
               | H: ∅ ⊨ ?v ∴ TBool, Hv: value ?v
                 |- _ => pose proof canon_bool v Hv H as (? & ?);
                         clear Hv; subst; simpl
               | H: rd ?e = Some _ |- context [rd ?e] => rewrite H; clear H
               | H: bound _ _ ∅ |- _ => unfold bound, "∅" in H; discriminate
               end;
        maybe_simpl; eauto;
          try (destruct e1; eauto; assumption);
          try (destruct e2; eauto; assumption);
          try (destruct e1; destruct e2; eauto; assumption);
          try (destruct e1; eauto;
               match goal with
               | H: _ ⊨ Nat _ ∴ TBool |- _ => inv H
               | H: _ ⊨ Bool _ ∴ TNat |- _ => inv H
               end; contradiction).
  Qed.
End Progress.

Section Sub.
  Local Hint Constructors typing : core.
  Hint Rewrite (@bind_same string typ) : core.

  Lemma weakening : forall g e t,
      g ⊨ e ∴ t -> forall g', incl g g' -> g' ⊨ e ∴ t.
  Proof.
    unfold incl, bound;
      intros g e t Hget; induction Hget;
        intros g' HI; unfold bound in *;
          simpl in *; eauto.
    - constructor. firstorder.
    - constructor.
      apply IHHget; intuition.
      unfold bind in *; repeat dispatch_eqdec; auto.
    - econstructor; eauto.
      apply IHHget2; intuition.
      unfold bind in *; repeat dispatch_eqdec; auto.
  Qed.
  
  Lemma empty_ctx : forall e t,
      ∅ ⊨ e ∴ t -> forall g, g ⊨ e ∴ t.
  Proof.
    intros e t H g.
    apply weakening with (g' := g) in H; auto.
    unfold incl, bound, "∅". discriminate.
  Qed.

  Local Hint Resolve empty_ctx : core.
  
  Lemma sub_lemma : forall e e' t t' x g,
      (x ↦ t';; g) ⊨ e ∴ t -> ∅ ⊨ e' ∴ t' -> g ⊨ ⟦x:=e'⟧ e ∴ t.
  Proof.
    intro e;
      induction e as
        [ x
        | x e IHe
        | e1 IHe1 e2 IHe2
        | n | b
        | e1 IHe1 e2 IHe2 e3 IHe3
        | o e1 IHe1 e2 IHe2
        | x e1 IHe1 e2 IHe2 ];
      intros e' t t' y g He He'; inv He; simpl;
        unfold bound in *; eauto.
    - dispatch_eqdec.
      + rewrite bind_sound in H0; inv H0; auto.
      + rewrite bind_complete in H0; auto.
    - dispatch_eqdec; autorewrite with core in *; eauto.
      rewrite bind_diff_comm in H2 by auto; eauto.
    - dispatch_eqdec; autorewrite with core in *; eauto.
      rewrite bind_diff_comm in H4 by auto; eauto.
  Qed.
End Sub.

Section Preservation.
  (* TODO *)
End Preservation.
