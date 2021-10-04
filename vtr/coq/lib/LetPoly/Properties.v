Require Export CoqRecon.LetPoly.Typing
        CoqRecon.Unify.Properties.

Section Props.
  Local Hint Constructors DM : core.
  Local Hint Resolve pres_op_typs : core.
  
  Lemma DM_constraint_sound : forall Γ e τ χ C,
      Γ ⫦ e ∴ τ ⊣ χ ≀ C ->
      forall σ, Forall (uncurry (satisfy σ)) C ->
           σ ◀ Γ ⫢ e ∴ σ † τ.
  Proof.
    intros g e t X C H.
    induction H as
        [ g b
        | g n
        | g x e T t X C HTX He IHe
        | g e1 e2 T t1 t2 X1 X2 C1 C2
            HX1X2 HX1t1 HX2t2 HT He1 IHe1 He2 IHe2
        | g e1 e2 e3 t1 t2 t3 X1 X2 X3 C1 C2 C3
            HX1X2 HX1X3 HX2X3 He1 IHe1 He2 IHe2 He3 IHe3
        | g o e1 e2 t1 t2 t t' X1 X2 C1 C2
            HX1X2 Hop He1 IHe1 He2 IHe2
        | g x TS WS t Hlu Hinst
        | g x e1 e2 t1 t2 X1 X2 C1 C2 su
            HX1X2 Hufy He1 IHe1 He2 IHe2 ];
      intros s HC; simpl; eauto.
    - apply IHe in HC; simpl in *.
      rewrite mask_nil in HC; auto.
    - inversion HC as [| [t1' t2'] C' Hh Ht Heqns]; subst; clear HC.
      rewrite Forall_app in Ht; destruct Ht as [HC1 HC2].
      apply IHe1 in HC1; apply IHe2 in HC2.
      unfold uncurry, satisfy in Hh; simpl in Hh.
      rewrite Hh in HC1; eauto.
    - inversion HC as [| [? ?] ? Hhd1 Htl Heqns]; subst; clear HC.
      inversion Htl as [| [? ?] ? Hhd2 HC Heqns]; subst; clear Htl.
      repeat rewrite Forall_app in HC.
      destruct HC as [[HC1 HC2] HC3].
      unfold uncurry, satisfy in Hhd1, Hhd2; simpl in Hhd1.
      apply IHe1 in HC1; rewrite Hhd1 in HC1.
      apply IHe2 in HC2; apply IHe3 in HC3.
      rewrite <- Hhd2 in HC3; auto.
    - inversion HC as [| [? ?] ? Hhd1 Htl Heqns]; subst; clear HC.
      inversion Htl as [| [? ?] ? Hhd2 HC Heqns]; subst; clear Htl.
      rewrite Forall_app in HC; destruct HC as [HC1 HC2].
      unfold uncurry, satisfy in Hhd1,Hhd2.
      apply IHe1 in HC1; apply IHe2 in HC2.
      rewrite <- Hhd1 in HC1; rewrite <- Hhd2 in HC2; eauto.
    - unfold Instantiates in Hinst; destruct Hinst as [Hl Hws].
      rewrite Forall_forall in Hws; simpl in *; inv HC.
      admit.
    - rewrite Forall_app in HC; destruct HC as [HC1 HC2].
      apply Unify_satisfies in Hufy as Hsu.
      apply IHe1 in Hsu; apply IHe2 in HC2.
      apply DM_gen with (XS := Generalize su g (su † t1)) in Hsu.
  Abort.

  Lemma DM_constraint_sound : forall Γ e τ χ σ,
      Γ ⊢W e ∴ τ ⊣ χ ≀ σ -> σ ◀ Γ ⫢ e ∴ σ † τ.
  Proof.
    intros g e t X s H;
      induction H as
        [ g b
        | g n
        | g e1 e2 e3 t1 t2 t3 X1 X2 X3 s s' s1 s2 s3
            HX1X2 HX1X3 HX2X3 Hus1' Hus He1 IHe1 He2 IHe2 He3 IHe3
        | g o e1 e2 t1 t2 t t' X1 X2 s1 s1' s2 s2'
            HX1X2 Hus1' Hus2' He1 IHe1 He2 IHe2
        | g x e T t X s HT He IHe
        | g e1 e2 T t1 t2 X1 X2 s s1 s2
            HX1X2 HX1t2 HX2t1 HT Hus He1 IHe1 He2 IHe2
        | g x TS WS t Hlu [Hl Hws]
        | g x e1 e2 t1 t2 X1 X2 s1 s2 HX1X2 He1 IHe1 He2 IHe2 ];
      simpl; auto.
    - apply Unify_satisfies in Hus1'; inv Hus1'.
      rename H1 into Ht1; inv H2.
      unfold uncurry, satisfy in Ht1; simpl in Ht1.
      apply Unify_satisfies in Hus; inv Hus.
      rename H1 into Ht2; inv H2.
      unfold uncurry, satisfy in Ht2.
  Abort.
End Props.
