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
  Local Hint Constructors rd : core.

  Theorem prog : forall e t,
      ∅ ⊨ e ∴ t -> value e \/ exists e', e -->  e'.
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
               | H: bound _ _ ∅ |- _ => unfold bound, "∅" in H; discriminate
               | H: _ ⊨ Bool ?b ∴ TBool
                 |- context [Cond (Bool ?b) _ _ -->  _] => destruct b; clear H
               end; eauto.
  Qed.
End Progress.

Section Sub.
  Local Hint Constructors typing : core.
  Hint Rewrite (@bind_same string typ) : core.

  Lemma weakening : forall g e t,
      g ⊨ e ∴ t -> forall g', inclu g g' -> g' ⊨ e ∴ t.
  Proof.
    unfold inclu, bound;
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
  Local Hint Constructors typing : core.
  Local Hint Constructors op_typs : core.
  Local Hint Resolve sub_lemma : core.

  Theorem preservation : forall e e',
      e -->  e' -> forall t, ∅ ⊨ e ∴ t -> ∅ ⊨ e' ∴ t.
  Proof.
    intros e e' Hee'; induction Hee'; intros t Ht; inv Ht;
      repeat match goal with
             | H: op_typs _ _ _ |- _ => inv H
             | H: _ ⊨ λ _ ⇒ _ ∴ _ |- _ => inv H
             | H: _ ⊨ Bool _ ∴ TNat |- _ => inv H
             | H: _ ⊨ Nat _ ∴ TBool |- _ => inv H
             end; eauto.
  Qed.
End Preservation.

Section EvalRd.
  Lemma eval_complete : forall e e',
    e -->  e' -> eval e = Some e'.
  Proof.
    intros e e' Hee'; induction Hee'; maybe_simpl; eauto.
    - rewrite IHHee'. destruct e1; eauto. inv Hee'.
    - rewrite IHHee'. destruct e1; eauto. inv Hee'.
    - rewrite IHHee'.
      destruct o; maybe_simpl; eauto;
        destruct e2; eauto; inv Hee'.
    - rewrite IHHee'.
      destruct o; maybe_simpl; eauto;
        destruct e2; eauto; inv Hee'.
    - rewrite IHHee'.
      destruct o; destruct e1;
        maybe_simpl; eauto;
          destruct e2; eauto; inv Hee'.
  Qed.

  Local Hint Constructors rd : core.

  Ltac unwind :=
    match goal with
    | H: match eval ?e with
         | Some _ => Some _
         | None   => None
         end = Some _ |- _ =>
      assert (exists e', eval e = Some e')
        by (destruct (eval e) as [? |] eqn:? ;
            try discriminate; eauto);
      match goal with
      | Hex: (exists e', eval ?e = Some e') |- _ =>
        destruct Hex as [? ?];
        match goal with
        | Heq: eval ?e = Some ?e' |- _ =>
          rewrite Heq in H
        end
      end
    end.
  
  Lemma eval_sound : forall e e',
      eval e = Some e' -> e -->  e'.
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
      intros e' Heval; simpl in *;
        maybe_simpl_hyp Heval; try discriminate.
    - destruct e1;
        maybe_simpl_hyp Heval;
        try discriminate;
        try unwind; inv Heval; eauto.
    - destruct e1;
        maybe_simpl_hyp Heval;
        try discriminate;
        try unwind; inv Heval; eauto.
      destruct b; inv H0; eauto.
    - destruct o; destruct e1;
        maybe_simpl_hyp Heval;
        try discriminate;
        try unwind; try (inv Heval; eauto; assumption);
          destruct e2; try discriminate;
            try unwind; inv Heval; eauto.
    - inv Heval; eauto.
  Qed.
End EvalRd.
