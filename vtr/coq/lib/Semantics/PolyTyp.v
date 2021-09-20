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

(*
Reserved Notation "p1 ≂ p2" (at level 70, no associativity).

Inductive alpha : poly -> poly -> Prop :=
| alpha_nil (t : typ) :
  t ≂ t
| alpha_cons X Y XS YS x y :
  (∀ XS, x) ≂ (∀ YS, (Y ↦ TVar X;; ∅) † y) ->
  (∀ (X :: XS), x) ≂ (∀ (Y :: YS), y)
where "p1 ≂ p2" := (alpha p1 p2) : type_scope.
  
Section Alpha.
  Local Hint Unfold Reflexive : core.
  Local Hint Constructors alpha : core.

  Lemma tsub_same_tvar : forall t T,
      (T ↦ TVar T;; ∅) † t = t.
  Proof.
    intro t;
      induction t as [| | t1 IHt1 t2 IHt2 | T];
      intro X; simpl in *; auto.
    - rewrite IHt1, IHt2; reflexivity.
    - unfold bind; dispatch_eqdec; reflexivity.
  Qed.

  Hint Rewrite tsub_same_tvar : core.
  
  Lemma alpha_reflexive : Reflexive alpha.
  Proof.
    autounfold with *; intros [XS x].
    generalize dependent x.
    induction XS as [| X XS IHXS]; intro x; auto.
    constructor; autorewrite with core; auto.
  Qed.

  Local Hint Unfold Symmetric : core.
  
  Lemma alpha_symmetric : Symmetric alpha.
  Proof.
    autounfold with *; intros [XS x] [YS y] H.
    induction H as [t | U V US VS u v Huv IH]; auto.
    inv Huv; inv IH.
    - constructor.

Definition alpha
           '(∀ XS, x : poly)
           '(∀ YS, y : poly) : Prop :=
  forall t,
    ~[ XS ⟼  repeat t (length XS) ]~ † x =
    ~[ YS ⟼  repeat t (length YS) ]~ † y.

Definition alpha_ex
           '(∀ XS, x : poly)
           '(∀ YS, y : poly) : Prop :=
  exists t,
    ~[ XS ⟼  repeat t (length XS) ]~ † x =
    ~[ YS ⟼  repeat t (length YS) ]~ † y.

Section Alpha.
  Local Hint Unfold alpha : core.
  Local Hint Unfold Reflexive : core.

  Lemma alpha_reflexive : Reflexive alpha.
  Proof.
    autounfold with *; intros [XS x]; intuition.
  Qed.

  Local Hint Unfold Symmetric : core.

  Lemma alpha_symmetric : Symmetric alpha.
  Proof.
    autounfold with *; intros [XS x] [YS y]; intuition.
  Qed.

  Local Hint Unfold Transitive : core.

  Lemma alpha_transitive : Transitive alpha.
  Proof.
    autounfold with *; intros [XS x] [YS y] [ZS z];
      etransitivity; eauto.
  Qed.

  Local Hint Unfold alpha_ex : core.
  
  Lemma alpha_alpha_ex : forall p q,
      alpha p q -> alpha_ex p q.
  Proof.
    autounfold with *; intros [XS x] [YS y] H.
    specialize H with 0; eauto.
  Qed.

  Lemma alpha_ex_alpha : forall p q,
      alpha_ex p q -> alpha p q.
  Proof.
    autounfold with *; intros [XS x] [YS y].
    generalize dependent YS;
      generalize dependent XS;
      generalize dependent y.
    induction x as [| | x1 IHx1 x2 IHx2 | X];
      intros [| | y1 y2 | Y] XS YS [w Hw] t; simpl in *;
        try discriminate; auto.
    generalize dependent τ;
      generalize dependent YS;
      generalize dependent XS;
      generalize dependent y.
    induction x as [| | x1 IHx1 x2 IHx2 | X];
      intros [| | y1 y2 | Y] XS YS τ H t; simpl in *;
        try discriminate; auto.
    - 
      generalize dependent Y;
        generalize dependent t;
        generalize dependent τ;
        generalize dependent YS.
      induction XS
End Alpha.

Definition typs_of_tvars : list nat -> list typ := map TVar.

Coercion typs_of_tvars : (list nat) >-> (list typ).
*)

(*
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
  x = ~[ YS ⟼  map TVar XS ]~ † y.

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

  Lemma tenv_tvars_involutive : forall XS YS,
      ~[ XS ⟼ map TVar YS ]~ ‡ ~[ YS ⟼ map TVar XS ]~ =
      match length XS with
      | O => ∅
      | S _ => fun T => Some (TVar T)
      end.
  Proof.
    intro XS; induction XS as [| X XS IHXS];
      intros [| Y YS]; extensionality T; cbn;
        unfold "∅"; auto.
    - specialize IHXS with []; cbn in IHXS.
      Locate "~[ _ ⟼  _ ]~".
      unfold combine_to_env in IHXS.
      Search (combine _ []).
      rewrite combine_nil in IHXS; simpl in IHXS.
      (*
    specialize IHXS with YS.
    apply equal_f with (x := T) in IHXS.
    unfold "‡", "∅", bind in *.
    repeat dispatch_eqdec.
*)
  Abort.

  Lemma tvars_tsub_tvar_involutive : forall XS YS T,
      ~[ XS ⟼  map TVar YS ]~
       † match ~[ YS ⟼  map TVar XS ]~ T with
         | Some τ => τ
         | None => T
         end = T.
  Proof.
    intros XS YS T.
    destruct (~[YS ⟼  map TVar XS ]~ T) as [t |] eqn:Heqt;
      try apply combine_binds_only_tvar in Heqt as HOT;
      try destruct HOT as [Z HZ]; subst; simpl.
    - destruct (~[ XS ⟼  map TVar YS ]~ Z) as [t |] eqn:Heqt';
        try apply combine_binds_only_tvar in Heqt' as HOT;
        try destruct HOT as [W HW]; subst; simpl.
      + admit.
      + admit.
    - destruct (~[ XS ⟼  map TVar YS ]~ T) as [t |] eqn:Heqt';
        try apply combine_binds_only_tvar in Heqt' as HOT;
        try destruct HOT as [W HW]; subst; simpl; auto.
*)
      
(*
  Lemma tvars_tsub_involutive : forall t XS YS,
      ~[ XS ⟼ map TVar YS ]~ † ~[ YS ⟼ map TVar XS ]~ † t = t.
  Proof.
    intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
      intros XS YS; simpl; auto.
    - rewrite IHt1, IHt2; reflexivity.
    - generalize dependent T;
        generalize dependent YS.
      induction XS as [| X XS IHXS];
        intros [| Y YS] T; cbn; auto.
      unfold bind at 2; dispatch_eqdec; auto.
      + unfold bind; dispatch_eqdec; auto.
      + specialize IHXS with YS T.
        destruct (~[YS ⟼  map TVar XS]~ T)
          as [t' |] eqn:Heqt';
          try apply combine_binds_only_tvar in Heqt' as HOT;
          unfold combine_to_env in *; rewrite Heqt'; simpl in *.
        * destruct HOT as [Z HZ]; subst; simpl in *.
          unfold bind; dispatch_eqdec; auto.
          destruct (to_env (combine XS (map TVar YS)) X)
            as [t'' |] eqn:Heqt'';
            try apply combine_binds_only_tvar in Heqt'' as HOT.
          -- destruct HOT as [Z HZ]; subst; inv IHXS.
             (* no apparent contradiction here. *)
             admit.
          -- inv IHXS. exfalso.
             (* there is some contradiction here *)
             admit.
        * simpl; unfold bind.
          dispatch_eqdec; auto.
          destruct (to_env (combine XS (map TVar YS)) X)
            as [t'' |] eqn:Heqt'';
            try apply combine_binds_only_tvar in Heqt'' as HOT.
          -- destruct HOT as [Z HZ]; subst; inv IHXS.
             (* there is some type of contradiction here. *)
             exfalso. admit.
          -- exfalso. admit.
             (* no apparent contradiction here...*)
  Abort.
  
  Local Hint Unfold Symmetric : core.

  Lemma alpha_symmetric : Symmetric alpha.
  Proof.
    autounfold with *; intros [XS x] [YS y] H.
    rewrite H.
End Alpha.

(** Alpha equivalence of [poly] *)
Definition alpha (p1 p2 : poly) : Prop :=
  satisfy ~[ pvars p1 ⟼  map TVar (pvars p2) ]~ (ptyp p1) (ptyp p2).

Notation "p1 ≂ p2"
  := (alpha p1 p2)
       (at level 70, no associativity) : type_scope.

Section Alpha.
  Local Hint Resolve satisfy_reflexive : core.

  Lemma alpha_reflexive : Reflexive alpha.
  Proof.
    intuition.
  Qed.

  Local Hint Resolve satisfy_symmetric : core.
  Local Hint Unfold alpha : core.
  Local Hint Unfold Symmetric : core.

  Lemma satisfy_swap_bind : forall x y X Y s w,
      binds_only_tvar s -> binds_only_tvar w ->
      (satisfy s x y -> satisfy w x y) ->
      satisfy (X ↦ TVar Y;; s) x y ->
      satisfy (Y ↦ TVar X;; w) x y.
  Proof.
    unfold satisfy.
    intro x; induction x as [| | x1 IHx1 x2 IHx2 | X'];
      intros [| | y1 y2 | Y'] X Y s w Hs Hw Hsw Hbind;
      simpl in *; auto; try discriminate.
    - unfold bind in *.
      repeat dispatch_eqdec; auto; try discriminate.
      clear Hsw. unfold binds_only_tvar in Hs.
      destruct (s Y) as [t |] eqn:HsY; subst; try discriminate.
      apply Hs in HsY as (Z & HZ). discriminate.
    - unfold bind in *.
      repeat dispatch_eqdec; auto; try discriminate.
      clear Hsw. unfold binds_only_tvar in Hs.
      destruct (s Y) as [t |] eqn:HsY; subst; try discriminate.
      apply Hs in HsY as (Z & HZ). discriminate.
    - (* injection Hsw as Hsw1 Hsw2. *)
      injection Hbind as Hb1 Hb2.
      admit. (* I know what I have to do,
                I don't know if I have the
                strength to do it :(. *)
    - exfalso. clear Hsw.
      unfold bind at 3 in Hbind.
      dispatch_eqdec; try discriminate.
      unfold binds_only_tvar in Hs.
      destruct (s Y') as [t |] eqn:HsY; subst; try discriminate.
      apply Hs in HsY as (Z & HZ). discriminate.
    - exfalso. clear Hsw.
      unfold bind in Hbind.
      dispatch_eqdec; try discriminate.
      unfold binds_only_tvar in Hs.
      destruct (s X') as [t |] eqn:HsX; subst; try discriminate.
      apply Hs in HsX as (Z & HZ). discriminate.
    - exfalso. clear Hsw.
      unfold bind in Hbind.
      dispatch_eqdec; try discriminate.
      unfold binds_only_tvar in Hs.
      destruct (s X') as [t |] eqn:HsX; subst; try discriminate.
      apply Hs in HsX as (Z & HZ). discriminate.
    - exfalso. clear Hsw.
      unfold bind in Hbind.
      dispatch_eqdec; try discriminate.
      unfold binds_only_tvar in Hs.
      destruct (s X') as [t |] eqn:HsX; subst; try discriminate.
      apply Hs in HsX as (Z & HZ). discriminate.
    - unfold bind in *.
      repeat dispatch_eqdec; auto.
      + unfold binds_only_tvar in *.
        destruct (s Y') as [t |] eqn:HsY;
          try (inv Hbind; contradiction).
        apply Hs in HsY as (Z & HZ); subst. inv Hbind.
        destruct (s Z) as [u |] eqn:Hsu;
          try apply Hs in Hsu as [U HU];
          destruct (w Z) as [v |] eqn:Hwv;
          try apply Hw in Hwv as [V HV];
          destruct (w Y') as [q |] eqn:Hwq;
          try apply Hw in Hwq as (Q & HQ); subst; auto.
  Abort.
  
  Lemma satisfy_flipped_vars : forall XS YS x y,
      satisfy ~[XS ⟼ map TVar YS]~ x y ->
      satisfy ~[YS ⟼ map TVar XS]~ x y.
  Proof.
    unfold combine_to_env, satisfy.
    intro XS; induction XS as [| X XS IHXS];
      intros [| Y YS] x y H; simpl in *; auto.
    generalize dependent Y;
      generalize dependent X;
      generalize dependent y.
    induction x as [| | x1 IHx1 x2 IHx2 | X'];
      intros [| | y1 y2 | Y'] X Y Hxy;
      simpl in *; auto; try discriminate.
    - exfalso; unfold bind in *.
  Abort.
  
  Lemma alpha_symmetric : Symmetric alpha.
  Proof.
    autounfold with core.
    intros [XS x] [YS y] Hxy; simpl in *.
    apply satisfy_symmetric.
  Abort.

  Local Hint Resolve satisfy_transitive : core.
  Local Hint Unfold Transitive : core.
  
  Lemma alpha_transitive : Transitive alpha.
  Proof.
    autounfold with core.
    intros [XS x] [YS y] [ZS z] Hxy Hyz; simpl in *.
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
