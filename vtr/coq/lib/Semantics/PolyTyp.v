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

Reserved Notation "C ⊩ t1 ≂ t2" (at level 70, no associativity).

Inductive alpha (C : list (nat * nat)) : typ -> typ -> Prop :=
| alpha_nat :
    C ⊩ TNat ≂ TNat
| alpha_bool :
    C ⊩ TBool ≂ TBool
| alpha_arrow τ1 τ2 ρ1 ρ2 :
    C ⊩ τ1 ≂ ρ1 ->
    C ⊩ τ2 ≂ ρ2 ->
    C ⊩ τ1 → τ2 ≂ ρ1 → ρ2
| alpha_var (X Y : nat) :
    X = Y \/ In (X, Y) C ->
    C ⊩ X ≂ Y
where "C ⊩ t1 ≂ t2" := (alpha C t1 t2) : type_scope.

Section Alpha.
  Local Hint Unfold Reflexive : core.
  Local Hint Constructors alpha : core.
  
  Lemma alpha_reflexive : forall C, Reflexive (alpha C).
  Proof.
    autounfold with *; intros C t;
      induction t as [| | t1 IHt1 t2 IHt2 | T]; auto.
  Qed.

  Local Hint Unfold Symmetric : core.

  (*Lemma alpha_symmetric : forall C, Symmetric (alpha C).
  Proof.
    autounfold with *; intros C x y Hxy;
      induction Hxy; intuition.
  Qed.*)
  
  Local Hint Resolve in_flipper : core.
  
  Lemma alpha_symmetric_flip : forall C x y,
      C ⊩ x ≂ y -> flipper C ⊩ y ≂ x.
  Proof.
    intros C x y Hxy; induction Hxy; intuition.
  Qed.

  Lemma alpha_transitive : forall XS YS x y,
      combine XS YS ⊩ x ≂ y ->
      forall ZS z,
        combine YS ZS ⊩ y ≂ z ->
        combine XS ZS ⊩ x ≂ z.
  Proof.
    intros XS YS x y Hxy; induction Hxy;
      intros ZS z Hyz; inv Hyz; auto.
    rename Y0 into Z.
    constructor.
    intuition; subst; auto.
    - right. admit.
    - right. admit.
    - right.
      apply in_combine_nth_error in H0 as (n & HXS  & HYS).
      apply in_combine_nth_error in H  as (m & HYS' & HZS).
      enough (Hndy: NoDup YS).
      pose proof nodup_nth_error _ _ Hndy _ _ _ HYS HYS'; subst.
      eauto using in_combine_index. admit.
  Abort.
End Alpha.

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
(*
Definition alpha
           '(∀ XS, x : poly)
           '(∀ YS, y : poly) : Prop :=
  x = ~[ uniques YS ⟼  map TVar (uniques XS) ]~ † y.

Notation "p1 ≂ p2"
  := (alpha p1 p2)
       (at level 70, no associativity) : type_scope.

Section Alpha.
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
  Local Hint Unfold alpha : core.
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
      +
  Abort.
      
  Lemma tvars_tsub_involutive : forall t XS YS,
      ~[ XS ⟼ map TVar YS ]~ † ~[ YS ⟼ map TVar XS ]~ † t = t.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros XS YS; simpl; auto.
    - rewrite IHt1, IHt2; reflexivity.
    -
  Abort.
  
  Local Hint Unfold Symmetric : core.

  Lemma alpha_symmetric : Symmetric alpha.
  Proof.
    autounfold with *; intros [XS x] [YS y] H.
    rewrite H.
  Abort.
End Alpha.
*)
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
    (*p ≂ p' ->*)
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
