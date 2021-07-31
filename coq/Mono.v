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

  Lemma succ_le : forall n m,
      S n <= m -> exists o, m = S o.
  Proof.
    intros n [| m] HSnm; try lia; eauto.
  Qed.
  
  Ltac cgen_ind :=
    match goal with
    | |- forall e g t M M' C,
        cgen M g e = Some (t,M',C) -> _
      => intro e;
      induction e as
        [ x
        | x e IHe
        | e1 IHe1 e2 IHe2
        | b | n
        | e1 IHe1 e2 IHe2 e3 IHe3
        | o e1 IHe1 e2 IHe2 ]; intros g t M M' C Hgen;
      simpl in *; maybe_simpl_hyp Hgen;
      (* var *)
      [ destruct (g x) as [tg |] eqn:Hgxeq; inv Hgen
      (* abs *)
      | destruct (cgen (S M) (x ↦ TVar M;; g)%env e)
        as [[[t' Me] C'] |] eqn:H; inv Hgen
      (* app *)
      | destruct (cgen M g e1)
        as [[[t1 M1] C1] |] eqn:He1;
        try discriminate;
        destruct (cgen M1 g e2)
          as [[[t2 M2] C2] |] eqn:He2; inv Hgen
      (* bool *)
      | inv Hgen
      (* nat *)
      | inv Hgen
      (* cond *)
      | destruct (cgen M g e1)
        as [[[t1 M1] C1] |] eqn:He1; try discriminate;
        destruct (cgen M1 g e2)
          as [[[t2 M2] C2] |] eqn:He2; try discriminate;
        destruct (cgen M2 g e3)
          as [[[t3 M3] C3] |] eqn:He3; inv Hgen
      (* op *)
      | destruct (typs_of_op o) as [to t'] eqn:Hop; simpl in *;
        destruct (cgen M g e1)
          as [[[t1 M1] C1] |] eqn:He1; try discriminate;
        destruct (cgen M1 g e2)
          as [[[t2 M2] C2] |] eqn:He2; inv Hgen ]
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
  
  Lemma cgen_M : forall e g t M M' C,
      cgen M g e = Some (t,M',C) ->
      M <= M'.
  Proof.
    cgen_ind; try lia.
    - apply IHe in H; lia.
    - apply IHe1 in He1; apply IHe2 in He2; lia.
    - apply IHe1 in He1; apply IHe2 in He2;
        apply IHe3 in He3; lia.
    - apply IHe1 in He1; apply IHe2 in He2; lia.
  Qed.

  Local Hint Resolve cgen_M : core.

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
  
  Lemma cgen_tvars : forall e g t M M' C,
      cgen M g e = Some (t,M',C) ->
      (forall x tx, g x = Some tx ->
               forall X, In X (tvars tx) -> X < M) ->
      forall X, In X (tvars t) -> X < M'.
  Proof.
    cgen_ind; intros Hg X HX; eauto; simpl in *; try lia.
    - destruct HX as [HMX | HX]; subst; eauto.
      eapply IHe in H; eauto; solve_dumb x Hg.
    - assert (M <= M1) by eauto.
      assert (M1 <= M2) by eauto.
      assert (M2 <= M') by eauto.
      assert (Hg1: forall x tx,
                 g x = Some tx ->
                 forall X : nat, In X (tvars tx) -> X < M1)
             by solve_dumber Hg.
      pose proof IHe2 _ _ _ _ _ He2 Hg1 as IH2; clear IHe2 He2 Hg1.
      apply IH2 in HX; lia.
    - apply typs_of_op_tvars_r in Hop;
        rewrite Hop in HX;
        simpl in HX; contradiction.
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
  
  Lemma cgen_Ctvars : forall e g t M M' C,
      cgen M g e = Some (t,M',C) ->
      (forall x tx, g x = Some tx ->
               forall X, In X (tvars tx) -> X < M) ->
      forall X, In X (Ctvars C) -> X < M'.
  Proof.
    cgen_ind; intros Hg X HX; eauto; simpl in *; try lia.
    - eapply IHe in H; eauto; try solve_dumb x Hg.
    - assert (M <= M1) by eauto.
      assert (M1 <= M2) by eauto.
      assert (M <= M2) by lia.
      repeat rewrite in_app_iff in HX.
      rewrite In_Ctvars_app in HX.
      assert (Hg1: forall x tx,
                 g x = Some tx ->
                 forall X : nat, In X (tvars tx) -> X < M1)
        by solve_dumber Hg.
      pose proof IHe1 _ _ _ _ _ He1 Hg  X as IH1; clear IHe1.
      pose proof IHe2 _ _ _ _ _ He2 Hg1 X as IH2; clear IHe2.
      pose proof cgen_tvars _ _ _ _ _ _ He1 Hg  X as Ht1.
      pose proof cgen_tvars _ _ _ _ _ _ He2 Hg1 X as Ht2.
      intuition; simpl in *; try lia.
    - assert (M <= M1) by eauto.
      assert (M1 <= M2) by eauto.
      assert (M2 <= M') by eauto.
      assert (M <= M') by lia.
      repeat rewrite in_app_iff in HX.
      repeat rewrite In_Ctvars_app in HX.
      assert (Hg1: forall x tx,
                 g x = Some tx ->
                 forall X : nat, In X (tvars tx) -> X < M1)
        by solve_dumber Hg.
      assert (Hg2: forall x tx,
                 g x = Some tx ->
                 forall X : nat, In X (tvars tx) -> X < M2)
        by solve_dumber Hg.
      pose proof IHe1 _ _ _ _ _ He1 Hg  X as IH1; clear IHe1.
      pose proof IHe2 _ _ _ _ _ He2 Hg1 X as IH2; clear IHe2.
      pose proof IHe3 _ _ _ _ _ He3 Hg2 X as IH3; clear IHe3.
      pose proof cgen_tvars _ _ _ _ _ _ He1 Hg  X as Ht1.
      pose proof cgen_tvars _ _ _ _ _ _ He2 Hg1 X as Ht2.
      pose proof cgen_tvars _ _ _ _ _ _ He3 Hg2 X as Ht3.
      intuition; simpl in *; try lia.
    - assert (M <= M1) by eauto.
      assert (M1 <= M') by eauto.
      assert (M <= M') by lia.
      apply typs_of_op_tvars_l in Hop.
      rewrite Hop in HX; simpl in *.
      repeat rewrite in_app_iff in HX.
      rewrite In_Ctvars_app in HX.
      assert (Hg1: forall x tx,
                 g x = Some tx ->
                 forall X : nat, In X (tvars tx) -> X < M1)
        by solve_dumber Hg.
      pose proof IHe1 _ _ _ _ _ He1 Hg  X as IH1; clear IHe1.
      pose proof IHe2 _ _ _ _ _ He2 Hg1 X as IH2; clear IHe2.
      pose proof cgen_tvars _ _ _ _ _ _ He1 Hg  X as Ht1.
      pose proof cgen_tvars _ _ _ _ _ _ He2 Hg1 X as Ht2.
      intuition; simpl in *; try lia.
  Qed.

  Local Hint Resolve cgen_Ctvars : core.
  Local Hint Constructors Permutation : core.
  Local Hint Resolve Permutation_app : core.
  Local Hint Resolve Permutation_cons_append : core.
  Local Hint Resolve Permutation_in : core.
  Local Hint Resolve Permutation_sym : core.
  Local Hint Resolve typs_of_op_sound : core.
  
  Theorem cgen_sound : forall e g t M M' C,
      cgen M g e = Some (t,M',C) ->
      (forall x tx, g x = Some tx ->
               forall X, In X (tvars tx) -> X < M) ->
      exists X, Permutation X (seq M (M' - M)) /\
           g ⊢ e ∈ t ⊣ X @ C.
  Proof.
    cgen_ind; intros Hg;
      try match goal with
          | |- context [?n - ?n]
            => replace (n - n) with 0 by lia
          end; eauto.
    - apply IHe in H as IH; try solve_dumb x Hg.
      destruct IH as [X [HP IH]].
      apply cgen_M in H as HM.
      apply succ_le in HM as HM'.
      destruct HM' as [M'' HM'']; subst.
      apply le_S_n in HM.
      assert (Hm: exists M''', S M''' = S M'' - M).
      { simpl.
        clear Hg x e IHe H IH g C t' HP X.
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
    - assert (M <= M1) by eauto.
      assert (M1 <= M2) by eauto.
      assert (M <= M2) by lia.
      apply IHe1 in He1 as IH1; eauto;
        destruct IH1 as [X1 [HP1 IH1]].
      apply IHe2 in He2 as IH2; try solve_dumber Hg;
        destruct IH2 as [X2 [HP2 IH2]].
      rewrite <- Minus.minus_Sn_m by lia.
      exists (M2 :: X1 ++ X2). split.
      + rewrite seq_S; simpl.
        replace (M + (M2 - M)) with M2 by lia.
        replace (M2 - M) with ((M1 - M) + (M2 - M1)) by lia.
        rewrite seq_app.
        replace (M + (M1 - M)) with M1 by lia; eauto.
      + constructor; auto.
        * (* intersect helper lemma for [seq]. *) admit.
        * (* helper lemma for [M] and [tvars] of [cgen] *) admit.
        * (* helper lemma for [M] and [tvars] of [cgen] *) admit.
        * repeat rewrite in_app_iff.
          intros [HX1 | [HX2 | [Ht1 | [Ht2 | [HC1 | HC2]]]]].
          -- assert (H': In M2 (seq M (M1 - M))) by eauto.
             rewrite in_seq in H'; lia.
          -- assert (H': In M2 (seq M1 (M2 - M1))) by eauto.
             rewrite in_seq in H'; lia.
          -- eapply cgen_tvars in He1; eauto; lia.
          -- eapply cgen_tvars in He2; eauto;
               try solve_dumber Hg; lia.
          -- eapply cgen_Ctvars in He1; eauto; lia.
          -- eapply cgen_Ctvars in He2; eauto;
               try solve_dumber Hg; lia.
    - assert (M <= M1) by eauto.
      assert (M1 <= M2) by eauto.
      assert (M2 <= M') by eauto.
      assert (M <= M') by lia.
      apply IHe1 in He1 as IH1; eauto;
        destruct IH1 as [X1 [HP1 IH1]].
      apply IHe2 in He2 as IH2; try solve_dumber Hg;
        destruct IH2 as [X2 [HP2 IH2]].
      apply IHe3 in He3 as IH3; try solve_dumber Hg;
        destruct IH3 as [X3 [HP3 IH3]].
      exists (X1 ∪ X2 ∪ X3)%set. split.
      + replace (M' - M) with
            ((M1 - M) + (M2 - M1) + (M' - M2)) by lia.
        repeat rewrite seq_app.
        replace (M + (M1 - M)) with M1 by lia.
        replace (M + (M1 - M + (M2 - M1))) with M2 by lia. eauto.
      + constructor; auto.
        * (* intersect helper lemma for [seq]. *) admit.
        * (* intersect helper lemma for [seq]. *) admit.
        * (* intersect helper lemma for [seq]. *) admit.
    - assert (M <= M1) by eauto.
      assert (M1 <= M') by eauto.
      assert (M <= M) by lia.
      apply IHe1 in He1 as IH1; eauto;
        destruct IH1 as [X1 [HP1 IH1]].
      apply IHe2 in He2 as IH2; try solve_dumber Hg;
        destruct IH2 as [X2 [HP2 IH2]].
      exists (X1 ++ X2). split.
      + replace (M' - M) with ((M1 - M) + (M' - M1)) by lia.
        rewrite seq_app.
        replace (M + (M1 - M)) with M1 by lia. eauto.
      + constructor; auto.
        (* intersect helper lemma for [seq]. *) admit.
  Admitted.
End CompSound.
