Require Export CoqRecon.Mono.

Open Scope maybe_scope.

Definition typs_of_op (o : op) : typ * typ :=
  match o with
  | And | Or  => (TBool, TBool)
  | Add | Sub => (TNat,  TNat)
  | Eq  | Lt  => (TNat,  TBool)
  end.

Fixpoint cgen (used : list nat) (g : gamma) (e : term)
  : option (typ * list nat * list (typ * typ)) :=
  match e with
  | Bool _ => Some (TBool,[],[])
  | Nat _  => Some (TNat,[],[])
  | Var x  => t ↤ g x;; (t,[],[])
  | (λ x ⇒ e)%term =>
    let F := 1 + list_max used in
    cgen (F :: used) (x ↦ TVar F;; g)%env e >>|
         fun '(t,X,C) => ((TVar F → t)%typ, F :: X, C)
  | (e1 ⋅ e2)%term =>
    cgen used g e1 >>=
         fun '(t1,X1,C1) =>
           cgen (used ++ X1) g e2 >>|
                fun '(t2,X2,C2) =>
                  let T := 1 + list_max (X1 ++ X2 ++ used) in
                  (TVar T, T :: X1 ++ X2,
                   (t1,(t2 → TVar T)%typ) :: C1 ++ C2)
  | Cond e1 e2 e3 =>
    cgen used g e1 >>=
         fun '(t1,X1,C1) =>
           cgen (used ++ X1) g e2 >>=
                fun '(t2,X2,C2) =>
                  cgen (used ++ X1 ++ X2) g e3 >>|
                       fun '(t3,X3,C3) =>
                         (t2, X1 ∪ X2 ∪ X3,
                          (t1,TBool) :: (t2,t3) :: C1 ∪ C2 ∪ C3)%set
  | Op o e1 e2 =>
    let (t,t') := typs_of_op o in
    cgen used g e1 >>=
         fun '(t1,X1,C1) =>
           cgen (used ++ X1) g e2 >>|
                fun '(t2,X2,C2) =>
                  (t', X1 ++ X2, (t,t1) :: (t,t2) :: C1 ++ C2)
  end.

Section CGEN.
  Local Hint Constructors op_typs : core.
  
  Lemma typs_of_op_sound : forall o t t',
      typs_of_op o = (t,t') -> op_typs o t t'.
  Proof.
    intros [] ? ? H; simpl in *;
      symmetry in H; inv H; auto.
  Qed.

  Lemma typs_of_op_complete : forall o t t',
      op_typs o t t' -> typs_of_op o = (t,t').
  Proof.
    intros o t t' H; inv H; simpl; reflexivity.
  Qed.

  Lemma typs_of_op_tvars_l : forall o t t',
      typs_of_op o = (t,t') -> tvars t = [].
  Proof.
    intros [] [] [] H; simpl in *;
      try discriminate; reflexivity.
  Qed.
  
  Lemma typs_of_op_tvars_r : forall o t t',
      typs_of_op o = (t,t') -> tvars t' = [].
  Proof.
    intros [] [] [] H; simpl in *;
      try discriminate; reflexivity.
  Qed.
  
  Lemma succ_le : forall n m,
      S n <= m -> exists o, m = S o.
  Proof.
    intros n [| m] HSnm; try lia; eauto.
  Qed.
  
  Local Hint Constructors constraint_typing : core.

  Ltac cgen_simpl :=
    match goal with
      | H: (match cgen ?F ?g ?e with
            | Some _ => _
            | None => _
            end = Some (_,_,_))
        |- _
        => destruct (cgen F g e)
          as [[[? ?] ?] |] eqn:?; simpl in *;
          try discriminate
    end.
  
  Ltac cgen_ind :=
    match goal with
    | |- forall e used g t X C,
        cgen used g e = Some (t,X,C) -> _
      => intro e;
      induction e as
        [ x
        | x e IHe
        | e1 IHe1 e2 IHe2
        | b | n
        | e1 IHe1 e2 IHe2 e3 IHe3
        | o e1 IHe1 e2 IHe2 ]; intros used g t X C Hgen;
      simpl in *; maybe_simpl_hyp Hgen;
      (* var *)
      [ destruct (g x) as [tg |] eqn:Hgxeq
      (* abs *)
      | cgen_simpl
      (* app *)
      | repeat cgen_simpl
      (* bool *)
      | idtac
      (* nat *)
      | idtac
      (* cond *)
      | repeat cgen_simpl
      (* op *)
      | destruct (typs_of_op o) as [to t'] eqn:Hop;
        simpl in *; repeat cgen_simpl ]; inv Hgen
    end.

  Ltac solve_dumb x Hg :=
    intros y ty Hgy Y HY;
    destruct (equiv_dec y x) as [Hxy | Hxy];
    unfold equiv, complement in *; simpl in *; subst;
    [ rewrite bind_sound in Hgy;
      inv Hgy; simpl in *; lia
    | rewrite bind_complete in Hgy by assumption;
      eapply Hg in Hgy; eauto; assumption ].

  Ltac solve_dumber Hg :=
    intros y ty Hgy Y HY; eapply Hg in Hgy; eauto; lia.

  Local Hint Resolve list_max_ge_in : core.

  Lemma cgen_used_X : forall e used g t X C,
      cgen used g e = Some (t,X,C) ->
      forall T, In T X -> list_max used < T.
  Proof.
    cgen_ind; intros T HX; simpl in *; try lia.
    - destruct HX as [HX | HX]; subst; try lia.
      eapply IHe with (T := T) in Heqo; eauto.
      replace (list_max (S (list_max used) :: used))
        with (list_max ([S (list_max used)] ++ used)) in Heqo by auto.
      rewrite list_max_app in Heqo. lia.
    - repeat rewrite list_max_app in HX.
      rewrite in_app_iff in HX.
      destruct HX as [HX | [HX | HX]]; subst; try lia.
      + eapply IHe1 in Heqo; eauto.
      + eapply IHe2 in Heqo0; eauto.
        rewrite list_max_app in Heqo0; lia.
    - repeat rewrite in_app_iff in HX.
      destruct HX as [[HX | HX] | HX].
      + eapply IHe1 in Heqo; eauto.
      + eapply IHe2 in Heqo0; eauto.
        rewrite list_max_app in Heqo0; lia.
      + eapply IHe3 in Heqo1; eauto.
        repeat rewrite list_max_app in Heqo1; lia.
    - rewrite in_app_iff in HX.
      destruct HX as [HX | HX]; subst; try lia.
      + eapply IHe1 in Heqo0; eauto.
      + eapply IHe2 in Heqo1; eauto.
        rewrite list_max_app in Heqo1; lia.
  Qed.

  Local Hint Resolve cgen_used_X : core.
  
  Lemma cgen_used : forall e used g t X C,
      cgen used g e = Some (t,X,C) ->
      forall T, In T used -> ~ In T X.
  Proof.
    intros e used g t X C Hgen T Hused HX.
    pose proof cgen_used_X _ _ _ _ _ _ Hgen _ HX.
    assert (T <= list_max used).
    { pose proof list_max_ge used as HM.
      rewrite Forall_forall in HM; eauto. }
    lia.
  Qed.

  Local Hint Resolve cgen_used : core.
  
  Lemma cgen_tvars : forall e used g t X C,
      cgen used g e = Some (t,X,C) ->
      (forall x t, g x = Some t -> (tvars t ⊆ used)%set) ->
      (tvars t ⊆ used ∪ X)%set.
  Proof.
    unfold "⊆".
    cgen_ind; intros Hg T HT; simpl in *;
      repeat rewrite in_app_iff in *;
      simpl in *; try lia; eauto.
    - destruct HT as [HT | HT]; subst; auto.
      eapply IHe in Heqo; eauto;
        try solve_dumb x Hg.
      simpl in Heqo. rewrite in_app_iff in Heqo.
      intuition.
    - eapply IHe2 in Heqo0; eauto.
      + repeat rewrite in_app_iff in Heqo0.
        intuition.
      + intros; rewrite in_app_iff; eauto.
    - erewrite typs_of_op_tvars_r in HT; eauto.
      simpl in HT; contradiction.
  Qed.

  Local Hint Resolve cgen_tvars : core.

  Lemma In_Ctvars_app : forall C1 C2 X,
      In X (Ctvars (C1 ∪ C2)%set) <-> In X (Ctvars C1) \/ In X (Ctvars C2).
  Proof.
    intro C1; induction C1 as [| [l1 r2] C1 IHC1];
      intros C2 X; simpl in *; intuition.
    - repeat rewrite in_app_iff in *.
      rewrite IHC1 in H. intuition.
    - repeat rewrite in_app_iff in *.
      rewrite IHC1. intuition.
    - repeat rewrite in_app_iff.
      rewrite IHC1. intuition.
  Qed.
  
  Lemma cgen_Ctvars : forall e used g t X C,
      cgen used g e = Some (t,X,C) ->
      (forall x t, g x = Some t -> (tvars t ⊆ used)%set) ->
      (Ctvars C ⊆ used ∪ X)%set.
  Proof.
    unfold "⊆".
    cgen_ind; intros Hg T HT; simpl in *;
      repeat rewrite in_app_iff in *;
      simpl in *; try lia; eauto.
    - eapply IHe in Heqo; eauto; try solve_dumb x Hg.
      rewrite in_app_iff in Heqo; simpl in *.
      intuition.
    - rewrite In_Ctvars_app in HT.
      rewrite in_app_iff. intuition.
      + eapply cgen_tvars in Heqo; eauto.
        unfold "⊆" in *. apply Heqo in H.
        rewrite in_app_iff in H. intuition.
      + eapply cgen_tvars in Heqo0; eauto; unfold "⊆" in *.
        * apply Heqo0 in H.
          repeat rewrite in_app_iff in H. intuition.
        * intros; rewrite in_app_iff; eauto.
      + eapply IHe1 in Heqo; eauto.
        rewrite in_app_iff in Heqo. intuition.
      + eapply IHe2 in Heqo0; eauto.
        * repeat rewrite in_app_iff in Heqo0.
          intuition.
        * intros; rewrite in_app_iff; eauto.
    - repeat rewrite In_Ctvars_app in HT.
      intuition.
      + eapply cgen_tvars in Heqo; eauto.
        unfold "⊆" in *. apply Heqo in H.
        rewrite in_app_iff in H.
        intuition.
      + eapply cgen_tvars in Heqo0; eauto; unfold "⊆" in *.
        * apply Heqo0 in H0.
          repeat rewrite in_app_iff in H0.
          intuition.
        * intros; rewrite in_app_iff; eauto.
      + eapply cgen_tvars in Heqo1; eauto; unfold "⊆" in *.
        * apply Heqo1 in H.
          repeat rewrite in_app_iff in H.
          intuition.
        * intros; rewrite in_app_iff; eauto.
      + eapply IHe1 in Heqo; eauto.
        rewrite in_app_iff in Heqo.
        intuition.
      + eapply IHe2 in Heqo0; eauto.
        * repeat rewrite in_app_iff in Heqo0.
          intuition.
        * intros; rewrite in_app_iff; eauto.
      + eapply IHe3 in Heqo1; eauto.
        * repeat rewrite in_app_iff in Heqo1.
          intuition.
        * intros; repeat rewrite in_app_iff; eauto.
    - rewrite In_Ctvars_app in HT.
      apply typs_of_op_tvars_l in Hop.
      repeat rewrite Hop in HT; simpl in *.
      intuition.
      + eapply cgen_tvars in Heqo0; eauto.
        apply Heqo0 in H0.
        rewrite in_app_iff in H0.
        intuition.
      + eapply cgen_tvars in Heqo1; eauto.
        * apply Heqo1 in H0.
          repeat rewrite in_app_iff in H0.
          intuition.
        * unfold "⊆"; intros; rewrite in_app_iff; eauto.
      + eapply IHe1 in Heqo0; eauto.
        rewrite in_app_iff in Heqo0.
        intuition.
      + eapply IHe2 in Heqo1; eauto.
        * repeat rewrite in_app_iff in Heqo1.
          intuition.
        * intros; rewrite in_app_iff; eauto.
  Qed.

  Local Hint Resolve cgen_Ctvars : core.
  
  Theorem cgen_sound : forall e used g t X C,
      cgen used g e = Some (t,X,C) ->
      (forall x t, g x = Some t -> (tvars t ⊆ used)%set) ->
      g ⊢ e ∈ t ⊣ X @ C.
  Proof.
    cgen_ind; intros Hg; eauto.
    - constructor; eauto.
      + eapply cgen_used in Heqo; eauto; intuition.
      + eapply IHe in Heqo; eauto. solve_dumb x Hg.
    - constructor; eauto.
      + apply Inter_nil; unfold Intersection.
        simpl; intro T; split; try contradiction.
        intros [HT1 HT2].
        eapply cgen_used_X in Heqo as H1; eauto.
        eapply cgen_used_X in Heqo0 as H2; eauto.
        rewrite list_max_app in H2.
        assert (T <= list_max l) by eauto; lia.
      + apply Inter_nil; unfold Intersection.
        simpl; intro T; split; try contradiction.
        intros [HT1 HT2].
        eapply cgen_used_X in Heqo as H1; eauto.
        eapply cgen_tvars in Heqo0 as H2; eauto.
        * apply H2 in HT2 as H'.
          repeat rewrite in_app_iff in H'.
          destruct H' as [[H' | H'] | H'].
          -- eapply cgen_used in Heqo; eauto.
          -- apply list_max_ge_in in H'.
             apply list_max_ge_in in HT2 as Htv. admit.
          -- eapply cgen_used_X in Heqo0 as H3; eauto.
             rewrite list_max_app in H3.
             apply list_max_ge_in in HT1. lia.
        * unfold "⊆" in *; intros; rewrite in_app_iff; eauto.
      + apply Inter_nil; unfold Intersection.
        simpl; intro T; split; try contradiction.
        intros [HT1 HT2].
        eapply cgen_tvars in Heqo as H1; eauto.
        eapply cgen_used_X in Heqo0 as H2; eauto.
        apply H1 in HT2 as H'.
        rewrite in_app_iff in H'.
        rewrite list_max_app in H2.
        destruct H' as [H' | H'].
        * eapply cgen_used in Heqo0; eauto.
        * eapply cgen_used_X in Heqo as H3; eauto.
          apply list_max_ge_in in H'. lia.
      + admit.
  Abort.
End CGEN.

Function unify
         (C : list (typ * typ))
         {measure C_size_vars C} : option tenv :=
  match C with
  | [] => Some ∅%env
  | (l, r) :: C =>
    if typ_eq l r then
      unify C
    else
      match l, r with
      | TVar L, _ =>
        if member L (tvars r) then
          None
        else
          let s' := (L ↦ r;; ∅)%env in
          s ↤ unify (Ctsub s' C);; (s ‡ s')%env
      | _, TVar R =>
        if member R (tvars l) then
          None
        else
          let s' := (R ↦ l;; ∅)%env in
          s ↤ unify (Ctsub s' C);; (s ‡ s')%env
      | (l → l')%typ,(r → r')%typ =>
        unify ((l,r) :: (l',r') :: C)
      | _, _ => None
      end
  end.
Proof.
  pose proof typ_size_vars_non_zero as Hnz.
  - intros; simpl.
    pose proof Hnz l; pose proof Hnz r. lia.
  - intros; simpl.
    clear r l p teq2 teq3 teq0 teq1 teq4 C teq.
    rename C0 into C.
    induction C as [| [l r] C IHC]; simpl; try lia.
    admit.
    (** Need lemma that shows for a type [τ],
       its measure [typ_size_vars] is no larger
       after a type substitution [X ↦ t;; ∅ ]
       when its type variable [X]
       does not appear free in [t],
       [[
       forall X t τ,
       ~ In X (tvars t) ->
       typ_size_vars ((X ↦ t;; ∅) † τ) <= typ_size_vars
       ]] *)
  - intros. admit.
  - intros; simpl. unfold typ_size_vars; simpl.
    repeat rewrite app_length. lia.
  - intros. admit.
  - intros. admit.
Abort.
