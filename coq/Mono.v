Require Export Coq.Strings.String
        Coq.Arith.PeanoNat CoqRecon.Env
        Coq.funind.Recdef CoqRecon.Maybe
        Coq.micromega.Lia.

Instance StringEqDec : EqDec string eq := {equiv_dec := string_dec}.
Instance NatEqDec
  : @EqDec nat (@eq nat) (@eq_equivalence nat) :=
  {equiv_dec := Nat.eq_dec}.

Inductive typ : Set :=
| TBool
| TNat
| TArrow : typ -> typ -> typ
| TVar : nat -> typ.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Notation "t1 → t2"
  := (TArrow t1 t2)
       (at level 30, right associativity) : typ_scope.

Fixpoint typ_size (t : typ) : nat :=
match t with
| TBool | TNat | TVar _ => 1
| (t → t')%typ => 1 + typ_size t + typ_size t'
end.

Lemma typ_size_non_zero : forall t,
    typ_size t > 0.
Proof.
  intro t; induction t; simpl; lia.
Qed.

Fixpoint tvars (t : typ) : list nat :=
  match t with
  | TBool | TNat => []
  | TVar T => [T]
  | (t → t')%typ => tvars t ++ tvars t'
  end.

Definition Ctvars : list (typ * typ) -> list nat :=
  fold_right (fun '(l,r) acc => tvars l ++ tvars r ++ acc) [].

Definition C_size : list (typ * typ) -> nat :=
  fold_right (fun '(l,r) acc => typ_size l + typ_size r + acc) 0.

Definition typ_size_vars (t : typ) : nat :=
  typ_size t + length (tvars t).

Lemma typ_size_vars_non_zero : forall t,
    typ_size_vars t > 0.
Proof.
  intros t; unfold typ_size_vars.
  pose proof typ_size_non_zero t; lia.
Qed.

Definition C_size_vars : list (typ * typ) -> nat :=
  fold_right
    (fun '(l,r) acc =>
       typ_size_vars l + typ_size_vars r + acc) 0.

Definition tenv : Set := @env nat typ.

Reserved Notation "s † t" (at level 20, right associativity).

Fixpoint tsub (σ : tenv) (t : typ) {struct t} : typ :=
  match t with
  | TBool => TBool
  | TNat => TNat
  | (t → t')%typ => (σ † t → σ † t')%typ
  | TVar T => match σ T with
             | Some τ => τ
             | None => TVar T
             end
  end
where "σ † t" := (tsub σ t) : typ_scope.

Lemma tsub_empty : forall t, (∅%env † t)%typ = t.
Proof.
  intro t; induction t; simpl in *; auto.
  rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

Definition tsub_compose (s1 s2 : tenv) : tenv :=
  env_map (tsub s1) s2.

Notation "s1 ‡ s2"
  := (tsub_compose s1 s2)
       (at level 21, left associativity) : env_scope.

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

Definition satisfy σ τ1 τ2 : Prop := (σ † τ1 = σ † τ2)%typ.

Lemma satisfy_reflexive : forall σ, Reflexive (satisfy σ).
Proof.
  unfold Reflexive, satisfy; reflexivity.
Qed.

Lemma satisfy_symmetric : forall σ, Symmetric (satisfy σ).
Proof.
  unfold Symmetric, satisfy; auto.
Qed.

Lemma satisfy_transitive : forall σ, Transitive (satisfy σ).
Proof.
  unfold Transitive, satisfy; intros; etransitivity; eauto.
Qed.

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

Definition gamma : Set := @env string typ.

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

Notation "s × g" := (env_map (tsub s) g)
                      (at level 25, right associativity) : env_scope.

Lemma tsub_gamma_empty : forall g : gamma, (∅ × g = g)%env.
Proof.
  intros g. extensionality n.
  unfold env_map.
  destruct (g n) eqn:Heq; auto.
  rewrite tsub_empty. reflexivity.
Qed.

Lemma tsub_gamma_twice : forall (s : tenv) (g : gamma),
    (s ‡ s × g = s × s × g)%env.
Proof.
  intros s g. extensionality T.
  unfold "×", env_map.
  destruct (g T) as [tg |] eqn:Heqtg; auto.
  f_equal. apply tsub_twice.
Qed.

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

Fail Fixpoint cgen (g : gamma) (e : term)
  : typ * list nat * list (typ * typ) :=
  match e with
  | Var x => _
  end.

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

Definition Ctsub (s : tenv) : list (typ * typ) -> list (typ * typ) :=
  map (fun '(l,r) => (s † l, s † r)%typ).

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

Fixpoint typ_eq (l r : typ) : bool :=
  match l, r with
  | TBool, TBool | TNat, TNat => true
  | TVar T1, TVar T2 => T1 =? T2
  | (l → l')%typ, (r → r')%typ
    => typ_eq l r && typ_eq l' r'
  | _, _ => false
  end.

Lemma typ_eq_reflexive : forall t, typ_eq t t = true.
Proof.
  Local Hint Resolve andb_true_intro : core.
  Local Hint Resolve Nat.eqb_refl : core.
  intro t; induction t as [| | t1 IHt1 t2 IHt2 | T];
    simpl; try reflexivity; auto.
Qed.
  
Lemma typ_eq_eq : forall l r,
    typ_eq l r = true -> l = r.
Proof.
  Hint Rewrite andb_true_iff : core.
  Hint Rewrite Nat.eqb_eq : core.
  intro l; induction l as [| | l IHl l' IHl' | L];
    intros [| | r r' | R] H; simpl in *;
      try discriminate; try reflexivity;
        autorewrite with core in *; f_equal; intuition.
Qed.

Open Scope maybe_scope.

Function unify (C : list (typ * typ)) {measure C_size_vars C} : option tenv :=
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
