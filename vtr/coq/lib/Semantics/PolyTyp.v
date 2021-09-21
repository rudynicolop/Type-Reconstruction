Require Export CoqRecon.Util.ListEnv CoqRecon.Semantics.DeclTyping.

(** Poly-types/type-schemes. *)
Record poly : Set :=
  { pvars : list nat; ptyp : typ }.

Definition pgamma : Set := list (string * poly).

Declare Scope poly_scope.
Delimit Scope poly_scope with poly.

Notation "∀ X , t"
  := ({| pvars := X; ptyp := t |})
       (at level 50, no associativity) : poly_scope.

Open Scope poly_scope.
Open Scope set_scope.

Definition ptvars '(∀ TS, t : poly) : list nat := tvars t ∖ TS.

Definition ftv : pgamma -> list nat :=
  fold_right (fun '(x,p) => app (ptvars p)) [].

Definition pnv (t : typ) : poly :=
  {| pvars := []; ptyp := t |}.

Coercion pnv : typ >-> poly.

Definition binds_only_tvar (s : tenv) : Prop :=
  forall X t, s X = Some t -> exists Y, t = TVar Y.

Lemma combine_binds_only_tvar : forall XS YS,
    binds_only_tvar ~[XS ⟼ map TVar YS]~.
Proof.
  unfold binds_only_tvar.
  intro XS; induction XS as [| X XS IHXS];
    intros [| Y YS] Z t H; cbn in *;
      unfold "∅" in *; try discriminate.
  unfold bind in H.
  dispatch_eqdec; inv H; eauto.
Qed.

Definition alpha
           '(∀ XS, x : poly)
           '(∀ YS, y : poly) : Prop :=
  x = ~[ uniques YS ⟼  map TVar (uniques XS) ]~ † y.

Notation "p1 ≂ p2"
  := (alpha p1 p2)
       (at level 70, no associativity) : type_scope.

Section AlphaExamples.
  Local Hint Unfold alpha : core.
  Local Hint Unfold combine_to_env : core.
  Local Hint Unfold bind : core.

  Ltac figure :=
    intros;
    repeat
      (autounfold with * in *; simpl in *; try dispatch_eqdec);
    auto.

  Ltac distinct_ex n :=
    match goal with
    | |- exists (_ : nat), _ => exists n; distinct_ex (S n)
    | |- _ => idtac
    end.

  Ltac dispute :=
    distinct_ex 0;
    match goal with
    | |- ~ _ => intros ?
    end; figure;
    try contradiction; try lia; try discriminate.
  
  Goal forall X Y, ∀ [X;Y], X → Y ≂ ∀ [Y;X], Y → X.
  Proof.
    figure.
  Qed.

  Goal forall X Y, ∀ [Y;X], Y → X ≂ ∀ [X;Y], X → Y.
  Proof.
    figure.
  Qed.

  Goal exists X Y Z, ~ ∀ [X;Y], X → Y ≂ ∀ [Z], Z → Z.
  Proof.
    dispute.
  Qed.

  Goal forall X Y Z : nat, ∀ [X], X → Y ≂ ∀ [X;Z], X → Y.
  Proof.
    figure.
  Qed.

  Goal forall X Y Z : nat, ∀ [X;Z], X → Y ≂ ∀ [X], X → Y.
  Proof.
    figure.
  Qed.
End AlphaExamples.

Section Alpha.
  Local Hint Unfold alpha : core.
    
  Lemma tvars_sub_tvar_same : forall TS T,
    match ~[ TS ⟼ map TVar TS ]~ T with
    | Some τ => τ
    | None => T
    end = T.
  Proof.
    intro TS; induction TS as [| X XS IHXS]; intro T; cbn; auto.
    unfold bind; dispatch_eqdec; eauto.
  Qed.

  Local Hint Resolve tvars_sub_tvar_same : core.
  
  Lemma tvars_tsub_same : forall t TS,
    ~[TS ⟼  map TVar TS]~ † t = t.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intro TS; simpl; auto; f_equal; auto.
  Qed.

  Local Hint Resolve tvars_tsub_same : core.
  Local Hint Unfold Reflexive : core.
  
  Lemma alpha_reflexive : Reflexive alpha.
  Proof.
    autounfold with core; intros [XS x]; auto.
  Qed.

  Lemma tvars_tsub_tvar_involutive : forall XS YS T,
      NoDup XS -> NoDup YS ->
      ~[XS ⟼  map TVar YS]~
       † match ~[YS ⟼  map TVar XS]~ T with
         | Some τ => τ
         | None => T
         end = T.
  Proof.
    intros XS YS T Hndx Hndy.
    destruct (~[YS ⟼  map TVar XS]~ T)
      as [t |] eqn:Heqt;
      try apply combine_binds_only_tvar in Heqt as HOT;
      try destruct HOT as [Z HZ]; subst; simpl.
    - destruct (~[XS ⟼  map TVar YS]~ Z)
        as [t |] eqn:Heqt';
        try apply combine_binds_only_tvar in Heqt' as HOT;
        try destruct HOT as [W HW]; subst; simpl.
      + rewrite combine_to_env_lookup in Heqt.
        rewrite combine_to_env_lookup in Heqt'.
        apply lookup_in in Heqt  as HT.
        apply lookup_in in Heqt' as HZ.
        rewrite combine_map_r in HT, HZ.
        rewrite in_map_iff in HT, HZ.
        destruct HT as ((x1 & x2) & H1 & HYX);
          destruct HZ as ((x3 & x4) & H2 & HXY);
          inv H1; inv H2.
        apply in_combine_flip in HYX.
        eauto using NoDup_pair_eq_r.
      + exfalso.
        rewrite combine_to_env_lookup in Heqt, Heqt'.
        apply lookup_in in Heqt as HT.
        apply lookup_not_in with (v:=TVar T) in Heqt' as HZ.
        rewrite combine_map_r in HT, HZ.
        rewrite in_map_iff in HT, HZ.
        destruct HT as ((x1 & x2) & Huv & HYXS); inv Huv.
        apply in_combine_flip in HYXS. firstorder.
    - destruct (~[XS ⟼  map TVar YS]~ T)
        as [t |] eqn:Heqt';
        try apply combine_binds_only_tvar in Heqt' as HOT;
        try destruct HOT as [W HW]; subst; simpl; auto.
      (* apply combine_to_env_some in Heqt'
        as (XS1 & XS2 & YS1 & YS2 & HC & HTXS1). *)
      rewrite combine_to_env_lookup in Heqt, Heqt'.
      pose proof lookup_not_in _ _ Heqt T as HT.
      apply lookup_in in Heqt' as HW.
      rewrite combine_map_r in HT, HW.
      rewrite in_map_iff in HT, HW.
      destruct HW as ((x1 & x2) & Huv & HYXS); inv Huv.
      apply nexists_forall_not with (x:=(T, T)) in HT.
      apply Decidable.not_and in HT; firstorder.
      apply not_in_combine in H.
      apply in_combine_nth_error in HYXS as (n & HXS & HYS).
      apply nth_error_In in HXS as HXSin;
        apply nth_error_In in HYS as HYSin.
      destruct H as [Htyxs | [Htyxs | [Htyxs | Hmn]]];
        try destruct Htyxs as [Htxs Htys];
        try destruct Hmn as (p & q & Hpq & Hp & Hq);
        try contradiction.
      + admit.
  Abort.
      
  Lemma tvars_tsub_involutive : forall t XS YS,
      NoDup XS -> NoDup YS ->
      ~[ XS ⟼ map TVar YS ]~ † ~[ YS ⟼ map TVar XS ]~ † t = t.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros XS YS Hndx Hndy; try (simpl; auto; assumption).
    - simpl; rewrite IHt1, IHt2; auto.
    - rewrite tsub_assoc.
      unfold "‡"; simpl.
      (* let X ≠ Y.
         ∴ (X ↦ Y) † (Y ↦ X) † X = (X ↦ Y) X = Y ≠ X.
         ∀ [X], X ≂ ∀ [Y], Y ↔ X = (Y ↦ X) † Y = X
         ∴ ∀ [X], X ≂ ∀ [Y], Y.
         ∀ [Y], Y ≂ ∀ [X], X ↔ Y = (X ↦ Y) † X = Y
         ∴ ∀ [Y], Y ≂ ∀ [X], X.
       *)
  Abort.
  
  Local Hint Unfold Symmetric : core.

  Lemma alpha_symmetric : Symmetric alpha.
  Proof.
    autounfold with *; intros [XS x] [YS y] H.
    generalize dependent YS;
      generalize dependent XS;
      generalize dependent y.
    induction x as [| | x1 IHx1 x2 IHx2 | X];
      intros [| | y1 y2 | Y] XS YS Hxy;
      try (simpl in *; try discriminate; auto; assumption).
    - simpl in *.
      destruct
        (~[ uniques YS ⟼ map TVar (uniques XS) ]~ Y)
        as [z |] eqn:Hz;
        try apply combine_binds_only_tvar in Hz as [Z HZ];
        subst; try discriminate.
    - simpl in *.
      destruct
        (~[ uniques YS ⟼ map TVar (uniques XS) ]~ Y)
        as [z |] eqn:Hz;
        try apply combine_binds_only_tvar in Hz as [Z HZ];
        subst; try discriminate.
    - simpl in *.
      injection Hxy as Hx1 Hx2.
      apply IHx1 in Hx1. apply IHx2 in Hx2.
      subst; reflexivity.
    - simpl in *.
      destruct
        (~[ uniques YS ⟼ map TVar (uniques XS) ]~ Y)
        as [z |] eqn:Hz;
        try apply combine_binds_only_tvar in Hz as [Z HZ];
        subst; try discriminate.
    - (* Either:
         1. [Y] is bound in [YS],
            & if [length XS <= length YS]
            the substitution is bijective;
            thus the goal is satisfied.
         2. [Y] is not bound in [YS],
            suggesting [X = Y],
            & [Y] is free in [∀ YS, y].
            a. [Y] is not bound in XS; thus trivial.
            b. [Y] is bound in [XS],
               & if [length YS <= length XS]
               & [Y] is not free in [∀ XS, x].
               then trouble starts, b/c
               [Y] will be mapped to some [W] in [YS].
               We know that [Y <> W] b/c
               [In W YS /\ ~ In Y YS]. *)
      (* An example of the problem:
         Consider [x = ∀ [X], X], [y = ∀ [Y], X].
         [X = (Y ↦ X) † X = X] whether or not [X = Y].
         ∴ by my def [∀ [X], X] ≂ ∀ [Y], X].
         This is bad because [x] is not alpha equivalent to [y].
         [X = (X ↦ Y) † X = Y] only makes sense if [X = Y].
         Thus my definition [≂] is flawed. *)
      simpl in *.
      destruct
        (~[ uniques YS ⟼ map TVar (uniques XS) ]~ Y)
        as [z |] eqn:Hz;
        try apply combine_binds_only_tvar in Hz as Hz';
        try destruct Hz' as [Z HZ].
      + subst. inv Hxy.
        destruct
          (~[ uniques XS ⟼ map TVar (uniques YS) ]~ Z)
          as [w |] eqn:Hw;
          try apply combine_binds_only_tvar in Hw as Hw';
          try destruct Hw' as [W HW]; subst.
        * (* provable. *) admit.
        * (* contradiction. *) admit.
      + inv Hxy.
        destruct
          (~[ uniques XS ⟼ map TVar (uniques YS) ]~ Y)
          as [w |] eqn:Hw;
          try apply combine_binds_only_tvar in Hw as Hw';
          try destruct Hw' as [W HW];
          subst; auto.
        (* stuck in the same way:
           provably [Y <> W];
           but the goal is [Y = W]. *)
      (*
    rewrite H.
    enough (XS = [0]).
    enough (YS = [1]).
    enough (x = 1).
    enough (y = 0).
    { subst.
      unfold uniques, remove,
      combine_to_env, combine,
      to_env, map, fold_right, uncurry in *.
      simpl in *. *)
  Abort.
End Alpha.

Reserved Notation "g ⫢ e ∴ p"
         (at level 70, no associativity).

Open Scope term_scope.

(** Damas Milner Declarative-typing system. *)
Inductive DM (Γ : pgamma) : term -> poly -> Prop :=
| DM_var x p :
    lookup x Γ = Some p ->
    Γ ⫢ x ∴ p
| DM_abs x e (τ τ' : typ) :
    ((x, pnv τ) :: Γ) ⫢ e ∴ τ' ->
    Γ ⫢ λ x ⇒ e ∴ τ → τ'
| DM_app e1 e2 (τ τ' : typ) :
    Γ ⫢ e1 ∴ τ → τ' ->
    Γ ⫢ e2 ∴ τ ->
    Γ ⫢ e1 ⋅ e2 ∴ τ'
| DM_let x e1 e2 p (τ : typ) :
    Γ ⫢ e1 ∴ p ->
    ((x, p) :: Γ) ⫢ e2 ∴ τ ->
    Γ ⫢ LetIn x e1 e2 ∴ τ
| DM_gen e XS (τ : typ) :
    Disjoint XS (ftv Γ) ->
    Γ ⫢ e ∴ τ ->
    Γ ⫢ e ∴ ∀ XS, τ
| DM_inst e (τ : typ) XS TS :
    Γ ⫢ e ∴ (∀ XS, τ) ->
    Γ ⫢ e ∴ ~[ XS ⟼  TS ]~ † τ
| DM_cond e1 e2 e3 p p' :
    p ≂ p' ->
    Γ ⫢ e1 ∴ TBool ->
    Γ ⫢ e2 ∴ p ->
    Γ ⫢ e3 ∴ p' ->
    Γ ⫢ Cond e1 e2 e3 ∴ p
| DM_op o e1 e2 τ τ' :
    op_typs o τ τ' ->
    Γ ⫢ e1 ∴ τ ->
    Γ ⫢ e2 ∴ τ ->
    Γ ⫢ Op o e1 e2 ∴ τ'
where "g ⫢ e ∴ p" := (DM g e p) : type_scope.
