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

Reserved Notation "p1 ≂ p2" (at level 70, no associativity).

Inductive alpha (p : poly) : poly -> Prop :=
| alpha_eq YS :
  Forall (fun Y => Y ∉ ptvars p) YS ->
  p ≂ ∀ YS, ~[pvars p ⟼  map TVar YS]~ † ptyp p
where "p1 ≂ p2" := (alpha p1 p2) : type_scope.

(*
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
*)

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

  (* Local Hint Resolve tvars_tsub_same : core. *)
  Local Hint Unfold Reflexive : core.
  Local Hint Constructors alpha : core.

  Lemma ptvars_same_Forall : forall XS x,
      Forall (fun Y : nat => Y ∉ ptvars (∀ XS, x)) XS.
  Proof.
    simpl; intro XS; induction XS as [| X XS IHXS];
      intro x; simpl in *; auto.
    constructor; simpl.
    - pose proof difference_Difference (tvars x) (X :: XS) as Hd.
      unfold Difference in Hd.
      intros H. firstorder.
    - rewrite Forall_forall.
      intros n HnXS Hin.
      specialize IHXS with x.
      rewrite Forall_forall in IHXS.
      specialize IHXS with n.
      apply IHXS in HnXS.
      rewrite remove_diff_cons in Hin.
      apply remove_sound in Hin. contradiction.
  Qed.

  Local Hint Resolve ptvars_same_Forall : core.
  
  Lemma alpha_reflexive : Reflexive alpha.
  Proof.
    autounfold with core; intros [XS x].
    rewrite <- tvars_tsub_same with (TS := XS) at 2.
    constructor; auto.
  Qed.

  Local Hint Unfold Symmetric : core.

  Lemma alpha_symmetric : Symmetric alpha.
  Proof.
    autounfold with *; intros [XS x] [YS y] H; inv H.
    rename H1 into H.
    pose proof tvars_tsub_same x YS as Hy.
    pose proof alpha_eq
         (∀ YS, ~[ XS ⟼ map TVar YS ]~ † x) XS as Ha; simpl in Ha.
  Abort.

  Local Hint Unfold Transitive : core.
  
  Lemma alpha_transitive : Transitive alpha.
  Proof.
    autounfold with *; intros [XS x] [YS y] [ZS z] Hxy Hyz.
    inv Hxy; inv Hyz.
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
