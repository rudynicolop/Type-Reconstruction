Require Export CoqRecon.Mono.

(** Completeness is never true :(. *)

Lemma tsub_twice : forall t s,
    ((s ‡ s)%env † t = s † s † t)%typ.
Proof.
  intro t;
    induction t as [| | t1 IHt1 t2 IHt2 | T];
    intros s; simpl; try reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - unfold "‡",env_map.
    destruct (s T) as [t |] eqn:HeqT; simpl; auto.
    rewrite HeqT. reflexivity.
Qed.

Lemma tsub_gamma_twice : forall (s : tenv) (g : gamma),
    (s ‡ s × g = s × s × g)%env.
Proof.
  intros s g. extensionality T.
  unfold "×", env_map.
  destruct (g T) as [tg |] eqn:Heqtg; auto.
  f_equal. apply tsub_twice.
Qed.

Section Complete.
  Local Hint Resolve sound : core.
  Local Hint Resolve preservation : core.
  Local Hint Resolve Subset_perm_l : core.
  Local Hint Resolve Subset_perm_r : core.
  Local Hint Resolve union_perm : core.
  Local Hint Constructors Permutation : core.

  Lemma tvars_subset : forall Γ e τ X C,
      Γ ⊢ e ∴ τ ⊣ X ≀ C -> (Ctvars C ⊆ X)%set.
  Proof.
    intros g e t X C H; induction H;
      simpl; try firstorder.
    - apply Subset_perm_l
        with (T :: tvars τ1 ∪ tvars τ2 ∪ Ctvars (C1 ∪ C2))%set.
      + rewrite <- app_assoc with (m := [T]); simpl.
        rewrite app_assoc.
        apply Permutation_middle.
      + apply Subset_cons. (** Dang. *) admit.
    - (** Same problem. *) admit.
    - (** Same problem. *) admit.
  Abort.

  (* Pierce's proof in TAPL relies upon this assumption. *)
  Lemma tsub_inverse : forall t s,
      exists t', (s † t')%typ = t /\ forall n, In n (tvars t') -> s n = None.
  Proof.
    intros t s;
      induction t as
        [| | t1 [t1' [IHt1 IHs1]] t2 [t2' [IHt2 IHs2]] | m].
    - exists TBool; intuition.
    - exists TNat; intuition.
    - exists (t1' → t2')%typ; simpl.
      rewrite IHt1, IHt2.
      split; [reflexivity |].
      intros n H. rewrite in_app_iff in H.
      intuition.
    - destruct (env_binds m s) as [HNone | [t HSome]].
      + exists (TVar m); simpl. rewrite HNone.
        intuition; subst; assumption.
      + (* Which is difficult to formally verify...*)
  Abort.

  (** I used Pierce's [CT-Abs-Inf] rule
      in place of [CT-Abs].
      It seems his form of completenss is impossible
      with this... *)
  Theorem complete_weak : forall Γ e t X C,
      Γ ⊢ e ∴ t ⊣ X ≀ C ->
      forall σ τ,
        (σ × Γ)%env ⊨ e ∴ τ ->
        (forall m, In m X -> σ m = None) ->
        exists σ', Forall (uncurry (satisfy σ')) C /\
              (σ' † t = τ)%typ /\ (mask σ' X = σ)%env.
  Proof.
    intros g e τ X C H; induction H;
      intros s t Ht Hd; inv Ht;
        try (exists s; intuition; assumption).
    - exists s; intuition.
      unfold bound,env_map in *.
      rewrite H in H1. inv H1.
      reflexivity.
    - (* This case is intractable.
         There is no way to use the induction hypothesis. *)
      admit.
    - apply IHconstraint_typing1 in H7 as IH1;
        [clear IHconstraint_typing1 H7 | intuition].
      apply IHconstraint_typing2 in H9 as IH2;
        [clear IHconstraint_typing2 H9 | intuition].
      destruct IH1 as [s1 [HC1 [Ht1 Hs1]]].
      destruct IH2 as [s2 [HC2 [Ht2 Hs2]]].
      assert (HX12: member T X1 = false /\ member T X2 = false).
      { repeat rewrite Not_In_member_iff; split;
          intros ?; apply H2; repeat rewrite in_app_iff;
            intuition. }
      destruct HX12 as [HX1 HX2].
      exists (fun Y =>
           if Y == T then Some t else
             if member Y X1 then s1 Y else
               if member Y X2 then s2 Y else s Y).
      repeat split.
      + constructor; simpl.
        * unfold satisfy; simpl.
          dispatch_eqdec.
          (* Need induction...probably...*) admit.
        * rewrite Forall_app; split.
          -- (* Need induction. *) admit.
          -- (* Need induction. *) admit.
      + simpl; dispatch_eqdec; reflexivity.
      + extensionality Y; unfold "∉"; simpl.
        destruct (equiv_dec Y T) as [HYT | HYT];
          unfold equiv, complement in *; subst. admit. admit.
    - apply IHconstraint_typing1 in H8 as IH1;
        [ clear IHconstraint_typing1 H8 | intuition ].
      apply IHconstraint_typing2 in H10 as IH2;
        [ clear IHconstraint_typing2 H10 | intuition ].
      apply IHconstraint_typing3 in H11 as IH3;
        [ clear IHconstraint_typing3 H11 | intuition ].
      destruct IH1 as [s1 [HC1 [Ht1 Hs1]]].
      destruct IH2 as [s2 [HC2 [Ht2 Hs2]]].
      destruct IH3 as [s3 [HC3 [Ht3 Hs3]]].
      exists (fun Y =>
           if member Y X1 then s1 Y else
             if member Y X2 then s2 Y else
               if member Y X3 then s3 Y else s Y).
      repeat split.
      + repeat constructor.
        * unfold satisfy, uncurry; simpl.
          (* Requires induction... *) admit.
        * unfold satisfy, uncurry; simpl.
          (* Requires induction... *) admit.
        * repeat rewrite Forall_app; repeat split.
          (* Requires induction...*) admit. admit. admit.
      + (* Nope. *) admit.
      + extensionality Y; unfold mask; simpl.
        destruct (member Y (X1 ∪ X2 ∪ X3)%set) eqn:HYmem.
        * symmetry; apply Hd; auto using member_In.
        * assert (HY123:
                    member Y X1 = false /\
                    member Y X2 = false /\
                    member Y X3 = false).
          { repeat rewrite Not_In_member_iff in *.
            repeat rewrite in_app_iff in HYmem.
            intuition. }
          destruct HY123 as [HY1 [HY2 HY3]].
          rewrite HY1,HY2,HY3. reflexivity.
      + apply Hd;
          repeat rewrite in_app_iff;
          intuition.
      + apply Hd;
          repeat rewrite in_app_iff;
          intuition.
    - (* Same stuff... *)
  Abort.
End Complete.
