Require Export Coq.Strings.String
        Coq.Arith.PeanoNat Coq.funind.Recdef
        CoqRecon.Maybe CoqRecon.Typ
        Coq.micromega.Lia.

Instance StringEqDec : EqDec string eq := {equiv_dec := string_dec}.
Instance NatEqDec
  : @EqDec nat (@eq nat) (@eq_equivalence nat) :=
  {equiv_dec := Nat.eq_dec}.

Inductive op : Set :=
| And | Or | Add | Sub | Eq | Lt.

Inductive op_typs : op -> typ -> typ -> Prop :=
| ot_and : op_typs And TBool TBool
| ot_or  : op_typs Or  TBool TBool
| ot_add : op_typs Add TNat  TNat
| ot_sub : op_typs Sub TNat  TNat
| ot_eq  : op_typs Eq  TNat  TBool
| ot_lt  : op_typs Lt  TNat  TBool.

Inductive term : Set :=
| Var : string -> term
| Abs : string -> term -> term
| App : term -> term -> term
| Bool : bool -> term
| Nat : nat -> term
| Cond : term -> term -> term -> term
| Op : op -> term -> term -> term.

Declare Scope term_scope.
Delimit Scope term_scope with term.

Notation "'λ' x ⇒ e"
  := (Abs x e)
       (at level 35, right associativity) : term_scope.
Notation "e1 ⋅ e2"
  := (App e1 e2)
       (at level 34, left associativity) : term_scope.

Reserved Notation "g ⊨ e ∈ t" (at level 70).

Inductive typing (Γ : gamma) : term -> typ -> Prop :=
| t_bool b :
    Γ ⊨ Bool b ∈ TBool
| t_nat n :
    Γ ⊨ Nat n ∈ TNat
| t_var x τ :
    bound x τ Γ ->
    Γ ⊨ Var x ∈ τ
| t_abs x e τ τ' :
    (x ↦ τ;; Γ)%env ⊨ e ∈ τ' ->
    Γ ⊨ (λ x ⇒ e)%term ∈ (τ → τ')%typ
| t_app e1 e2 τ τ' :
    Γ ⊨ e1 ∈ (τ → τ')%typ ->
    Γ ⊨ e2 ∈ τ ->
    Γ ⊨ (e1 ⋅ e2)%term ∈ τ'
| t_cond e1 e2 e3 τ :
    Γ ⊨ e1 ∈ TBool ->
    Γ ⊨ e2 ∈ τ ->
    Γ ⊨ e3 ∈ τ ->
    Γ ⊨ Cond e1 e2 e3 ∈ τ
| t_op o e1 e2 τ τ' :
    op_typs o τ τ' ->
    Γ ⊨ e1 ∈ τ ->
    Γ ⊨ e2 ∈ τ ->
    Γ ⊨ Op o e1 e2 ∈ τ'
where "g ⊨ e ∈ t" := (typing g e t).

Section Prez.
  Local Hint Constructors op_typs : core.

  Lemma pres_op_typs : forall o τ τ',
      op_typs o τ τ' ->
      forall σ, op_typs o (σ † τ)%typ (σ † τ')%typ.
  Proof.
    intros o t t' H s; inv H; simpl; auto.
  Qed.

  Local Hint Resolve pres_op_typs : core.
  Local Hint Constructors typing : core.
  
  Theorem preservation : forall Γ e τ,
    Γ ⊨ e ∈ τ -> forall σ,
      (σ × Γ)%env ⊨ e ∈ (σ † τ)%typ.
  Proof.
    intros g e t H;
      induction H; intros s; simpl in *; eauto.
    - constructor. unfold bound, env_map in *.
      rewrite H. reflexivity.
    - constructor.
      rewrite env_map_bind; auto.
  Qed.
End Prez.

Reserved Notation "g ⊢ e ∈ t ⊣ X @ C" (at level 70).

Inductive constraint_typing (Γ : gamma)
  : term -> typ -> list nat -> list (typ * typ) -> Prop :=
| ct_bool b :
    Γ ⊢ Bool b ∈ TBool ⊣ [] @ []
| ct_nat n :
    Γ ⊢ Nat n ∈ TNat ⊣ [] @ []
| ct_var x τ :
    bound x τ Γ ->
    Γ ⊢ Var x ∈ τ ⊣ [] @ []
| ct_abs x e T τ X C :
    ~ In T X ->
    (x ↦ TVar T ;; Γ)%env ⊢ e ∈ τ ⊣ X @ C ->
    Γ ⊢ (λ x ⇒ e)%term ∈ (TVar T → τ)%typ ⊣ (T :: X) @ C
| ct_app e1 e2 T τ1 τ2 X1 X2 C1 C2 :
    (X1 ∩ X2)%set = [] ->
    (X1 ∩ tvars τ2)%set = [] ->
    (X2 ∩ tvars τ1)%set = [] ->
    ~ In T (X1 ++ X2 ++ tvars τ1 ++ tvars τ2 ++ Ctvars C1 ++ Ctvars C2) ->
    Γ ⊢ e1 ∈ τ1 ⊣ X1 @ C1 ->
    Γ ⊢ e2 ∈ τ2 ⊣ X2 @ C2 ->
    Γ ⊢ (e1 ⋅ e2)%term ∈ TVar T
      ⊣ (T :: X1 ∪ X2)%set
      @ ((τ1, (τ2 → TVar T)%typ) :: C1 ∪ C2)%set
| ct_cond e1 e2 e3 τ1 τ2 τ3 X1 X2 X3 C1 C2 C3 :
    (X1 ∩ X2)%set = [] ->
    (X1 ∩ X3)%set = [] ->
    (X2 ∩ X3)%set = [] ->
    Γ ⊢ e1 ∈ τ1 ⊣ X1 @ C1 ->
    Γ ⊢ e2 ∈ τ2 ⊣ X2 @ C2 ->
    Γ ⊢ e3 ∈ τ3 ⊣ X3 @ C3 ->
    Γ ⊢ Cond e1 e2 e3 ∈ τ2
      ⊣ (X1 ∪ X2 ∪ X3)%set
      @ ((τ1,TBool) :: (τ2,τ3) :: C1 ∪ C2 ∪ C3)%set
| ct_op o e1 e2 τ1 τ2 τ τ' X1 X2 C1 C2 :
    (X1 ∩ X2)%set = [] ->
    op_typs o τ τ' ->
    Γ ⊢ e1 ∈ τ1 ⊣ X1 @ C1 ->
    Γ ⊢ e2 ∈ τ2 ⊣ X2 @ C2 ->
    Γ ⊢ Op o e1 e2 ∈ τ'
      ⊣ (X1 ∪ X2)%set
      @ ((τ,τ1) :: (τ,τ2) :: C1 ∪ C2)%set
where "g ⊢ e ∈ t ⊣ X @ C"
        := (constraint_typing g e t X C).

Section Sound.
  Local Hint Constructors op_typs : core.
  Local Hint Constructors typing : core.
  Local Hint Resolve preservation : core.
  Local Hint Resolve pres_op_typs : core.
  
  Theorem sound : forall Γ e t X C,
    Γ ⊢ e ∈ t ⊣ X @ C ->
    forall σ,
      Forall (uncurry (satisfy σ)) C ->
      (σ × Γ)%env ⊨ e ∈ (σ † t)%typ.
  Proof.
    intros g e t X C H; induction H; intros s HC; eauto.
    - apply IHconstraint_typing in HC.
      constructor. fold tsub.
      rewrite <- env_map_bind in HC.
      assumption.
    - inv HC. rewrite Forall_app in H8.
      destruct H8 as [HC1 HC2].
      unfold uncurry, satisfy in H7.
      apply IHconstraint_typing1 in HC1.
      apply IHconstraint_typing2 in HC2.
      rewrite H7 in HC1. eauto.
    - inv HC. inv H8.
      repeat rewrite Forall_app in H10.
      destruct H10 as [[HC1 HC2] HC3].
      apply IHconstraint_typing1 in HC1.
      apply IHconstraint_typing2 in HC2.
      apply IHconstraint_typing3 in HC3.
      unfold uncurry, satisfy in *; simpl in *.
      rewrite H7 in HC1. rewrite <- H9 in HC3. auto.
    - inv HC. inv H6.
      rewrite Forall_app in H8.
      destruct H8 as [HC1 HC2].
      apply IHconstraint_typing1 in HC1.
      apply IHconstraint_typing2 in HC2.
      unfold uncurry,satisfy in *.
      rewrite <- H5 in HC1; rewrite <- H7 in HC2. eauto.
  Qed.
End Sound.

Inductive Unify : list (typ * typ) -> tenv -> Prop :=
| Unify_nil :
    Unify [] ∅%env
| Unify_cons_skip τ C σ :
    Unify C σ ->
    Unify ((τ,τ) :: C) σ
| Unify_cons_var_l T τ C σ :
    ~ In T (tvars τ) ->
    let s := (T ↦ τ;; ∅)%env in
    Unify (Ctsub s C) σ ->
    Unify ((TVar T, τ) :: C) (σ ‡ s)%env
| Unify_cons_var_r τ T C σ :
    ~ In T (tvars τ) ->
    let s := (T ↦ τ;; ∅)%env in
    Unify (Ctsub s C) σ ->
    Unify ((τ , TVar T) :: C) (σ ‡ s)%env
| Unify_cons_arrow t t' τ τ' C σ :
    Unify ((t,τ) :: (t',τ') :: C) σ ->
    Unify ((t → τ, t' → τ')%typ :: C) σ.

Open Scope maybe_scope.

Definition typs_of_op (o : op) : typ * typ :=
  match o with
  | And | Or  => (TBool, TBool)
  | Add | Sub => (TNat,  TNat)
  | Eq  | Lt  => (TNat,  TBool)
  end.

Fixpoint cgen (M : nat) (g : gamma) (e : term)
  : option (typ * nat * list (typ * typ)) :=
  match e with
  | Bool _ => Some (TBool,M,[])
  | Nat _  => Some (TNat,M,[])
  | Var x  => t ↤ g x;; (t,M,[])
  | (λ x ⇒ e)%term =>
    cgen (S M) (x ↦ TVar M;; g)%env e >>|
         fun '(t,X,C) => ((TVar M → t)%typ, X, C)
  | (e1 ⋅ e2)%term =>
    cgen M g e1 >>=
         fun '(t1,M1,C1) =>
           cgen M1 g e2 >>|
                fun '(t2,M2,C2) =>
                  (TVar M2, S M2,
                   (t1,(t2 → TVar M2)%typ) :: C1 ++ C2)
  | Cond e1 e2 e3 =>
    cgen M g e1 >>=
         fun '(t1,M1,C1) =>
           cgen M1 g e2 >>=
                fun '(t2,M2,C2) =>
                  cgen M2 g e3 >>|
                       fun '(t3,M3,C3) =>
                         (t2, M3,
                          (t1,TBool) :: (t2,t3) :: C1 ∪ C2 ∪ C3)%set
  | Op o e1 e2 =>
    let (t,t') := typs_of_op o in
    cgen M g e1 >>=
         fun '(t1,M1,C1) =>
           cgen M1 g e2 >>|
                fun '(t2,M2,C2) =>
                  (t', M2, (t,t1) :: (t,t2) :: C1 ++ C2)
  end.

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

Section CompSound.
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

  Local Hint Constructors constraint_typing : core.

  Lemma cgen_M : forall e g t M M' C,
      cgen M g e = Some (t,M',C) ->
      M <= M'.
  Proof.
    intro e;
      induction e as
        [ x
        | x e IHe
        | e1 IHe1 e2 IHe2
        | b | n
        | e1 IHe1 e2 IHe2 e3 IHe3
        | o e1 IHe1 e2 IHe2 ]; intros g t M M' C Hgen;
        simpl in *; maybe_simpl_hyp Hgen.
    - destruct (g x) as [tg |] eqn:Hgxeq; inv Hgen; lia.
    - destruct (cgen (S M) (x ↦ TVar M;; g)%env e)
        as [[[t' Me] C'] |] eqn:H; inv Hgen.
      apply IHe in H. lia.
    - destruct (cgen M g e1)
        as [[[t1 M1] C1] |] eqn:He1;
        try discriminate.
      destruct (cgen M1 g e2)
        as [[[t2 M2] C2] |] eqn:He2; inv Hgen.
      apply IHe1 in He1. apply IHe2 in He2. lia.
    - inv Hgen. lia.
    - inv Hgen. lia.
    - destruct (cgen M g e1)
        as [[[t1 M1] C1] |] eqn:He1;
        try discriminate.
      destruct (cgen M1 g e2)
        as [[[t2 M2] C2] |] eqn:He2;
        try discriminate.
      destruct (cgen M2 g e3)
        as [[[t3 M3] C3] |] eqn:He3; inv Hgen.
      apply IHe1 in He1; apply IHe2 in He2;
        apply IHe3 in He3; lia.
    - destruct (typs_of_op o) as [to t']; simpl in *.
      destruct (cgen M g e1)
        as [[[t1 M1] C1] |] eqn:He1;
        try discriminate.
      destruct (cgen M1 g e2)
        as [[[t2 M2] C2] |] eqn:He2; inv Hgen.
      apply IHe1 in He1. apply IHe2 in He2. lia.
  Qed.

  Lemma succ_le : forall n m,
      S n <= m -> exists o, m = S o.
  Proof.
    intros n [| m] HSnm; try lia; eauto.
  Qed.

  Local Hint Constructors Permutation : core.
  Local Hint Resolve typs_of_op_sound : core.

  Theorem cgen_sound : forall e g t M M' C,
      cgen M g e = Some (t,M',C) ->
      exists X, Permutation X (seq M (M' - M)) /\
           g ⊢ e ∈ t ⊣ X @ C.
  Proof.
    intro e;
      induction e as
        [ x
        | x e IHe
        | e1 IHe1 e2 IHe2
        | b | n
        | e1 IHe1 e2 IHe2 e3 IHe3
        | o e1 IHe1 e2 IHe2 ]; intros g t M M' C H;
        simpl in *; maybe_simpl_hyp H.
    - destruct (g x) as [t' |] eqn:Hgx;
        simpl in *; inv H.
      replace (M' - M') with 0 by lia. eauto.
    - destruct (cgen (S M) (x ↦ TVar M;; g)%env e)
        as [[[t' Me] C'] |] eqn:HeqIH; inv H.
      apply IHe in HeqIH as IH.
      destruct IH as [X [HP IH]].
      apply cgen_M in HeqIH as HM.
      apply succ_le in HM as HM'.
      destruct HM' as [M'' HM'']; subst.
      apply le_S_n in HM.
      assert (Hm: exists M''', S M''' = S M'' - M).
      { simpl.
        clear x e IHe HeqIH IH g C t' HP X.
        induction M as [| M IHM]; eauto.
        destruct IHM as [Mx IHM]; try lia.
        destruct M as [| M].
        - inv IHM. exists (M'' - 1). lia.
        - exists (Mx - 1). lia. }
      destruct Hm as [M''' Hm]. rewrite <- Hm.
      rewrite <- cons_seq. exists (M :: X).
      replace M''' with (S M'' - S M) by lia.
      split; eauto. constructor.
      + intros HIn.
        eapply Permutation_in in HP; eauto.
        rewrite in_seq in HP. lia.
      + simpl in IH.
        rewrite <- Minus.minus_Sn_m in Hm by lia.
        inv Hm. assumption.
    - destruct (cgen M g e1)
        as [[[t1 M1] C1] |] eqn:He1; try discriminate.
      destruct (cgen M1 g e2)
        as [[[t2 M2] C2] |] eqn:He2; inv H.
      apply IHe1 in He1 as IH1;
        destruct IH1 as [X1 [HP1 IH1]].
      apply IHe2 in He2 as IH2;
        destruct IH2 as [X2 [HP2 IH2]].
      assert (HM2: M <= M2).
      { apply cgen_M in He1.
        apply cgen_M in He2. lia. }
      rewrite <- Minus.minus_Sn_m by lia.
      exists (M2 :: X1 ++ X2). split.
      + (* tedious, mechanical proof. *) admit.
      + constructor; auto.
        * (* intersect helper lemma for [seq]. *) admit.
        * (* helper lemma for [M] and [tvars] of [cgen] *) admit.
        * (* helper lemma for [M] and [tvars] of [cgen] *) admit.
        * repeat rewrite in_app_iff.
          (* tedious, mechanical proof. *) admit.
    - inv H. replace (M' - M') with 0 by lia; simpl; eauto.
    - inv H. replace (M' - M') with 0 by lia; simpl; eauto.
    - destruct (cgen M g e1)
        as [[[t1 M1] C1] |] eqn:He1; try discriminate.
      destruct (cgen M1 g e2)
        as [[[t2 M2] C2] |] eqn:He2; try discriminate.
      destruct (cgen M2 g e3)
        as [[[t3 M3] C3] |] eqn:He3; inv H.
      apply IHe1 in He1 as IH1;
        destruct IH1 as [X1 [HP1 IH1]].
      apply IHe2 in He2 as IH2;
        destruct IH2 as [X2 [HP2 IH2]].
      apply IHe3 in He3 as IH3;
        destruct IH3 as [X3 [HP3 IH3]].
      exists (X1 ∪ X2 ∪ X3)%set. split.
      + (* tedious, mechanical proof. *) admit.
      + constructor; auto.
        * (* intersect helper lemma for [seq]. *) admit.
        * (* intersect helper lemma for [seq]. *) admit.
        * (* intersect helper lemma for [seq]. *) admit.
    - destruct (typs_of_op o) as [to t'] eqn:Heqop.
      destruct (cgen M g e1)
        as [[[t1 M1] C1] |] eqn:He1; try discriminate.
      destruct (cgen M1 g e2)
        as [[[t2 M2] C2] |] eqn:He2; inv H.
      apply IHe1 in He1 as IH1;
        destruct IH1 as [X1 [HP1 IH1]].
      apply IHe2 in He2 as IH2;
        destruct IH2 as [X2 [HP2 IH2]].
      exists (X1 ++ X2). split.
      + (* tedious, mechanical proof. *) admit.
      + constructor; auto.
        (* intersect helper lemma for [seq]. *) admit.
  Admitted.
End CompSound.
