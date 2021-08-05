Require Export CoqRecon.EqDecInst CoqRecon.Typ Coq.funind.Recdef.

Open Scope maybe_scope.

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

Lemma mul_S : forall a b c d : nat,
    a <= b -> c <= d ->
    a * (S c) <= b * (S d).
Proof.
  intros a b c d Hab;
    generalize dependent d;
    generalize dependent c.
  induction Hab;
    intros c d Hcd; inv Hcd; try lia.
  - apply Nat.mul_le_mono_l; lia.
  - specialize IHHab with (c := d) (d := d). lia.
  - specialize IHHab with (c := c) (d := m0). lia.
Qed.

Corollary mul_S_same : forall a b : nat,
    a <= b -> a * S a <= b * S b.
Proof.
  auto using mul_S.
Qed.

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
  pose proof typ_size_non_zero as Hnz.
  - intros C p C' l r Hp HC Hlr; subst.
    unfold C_size_vars; simpl.
    pose proof Hnz l as Hl. pose proof Hnz r as Hr.
    pose proof remove_dups_length_app_r
         (tvars l ++ tvars r) (Ctvars C') as H'.
    rewrite app_assoc.
    pose proof mul_S_same _ _ H' as H''.
    apply Plus.plus_le_lt_compat; auto; lia.
  - intros C p C' l r Heql R Heqr Heqp HeqC _ _;
      subst; simpl in *.
    unfold C_size_vars; simpl.
    repeat rewrite app_length.
    pose proof In_member_reflects R (Ctvars C') as HRC'; inv HRC';
      unfold NatEqDec, nat_eq_eqdec in *.
    + rewrite <- H; simpl. admit.
    + rewrite <- H; simpl.
      rewrite Ctsub_not_in_tvars by auto.
      rewrite Ctsub_empty. lia.
  - intros C p C' l r Heql R Heqr Heqp HeqC _ _;
      simpl in *; subst.
    unfold C_size_vars; simpl.
    repeat rewrite app_length.
    pose proof In_member_reflects R (Ctvars C') as HRC'; inv HRC';
      unfold NatEqDec, nat_eq_eqdec in *.
    + rewrite <- H; simpl. admit.
    + rewrite <- H; simpl.
      rewrite Ctsub_not_in_tvars by auto.
      rewrite Ctsub_empty. lia.
  - intros C p C' l r l1 l2 Heql r1 e2 Heqr Heqp HeqC Htyp_eq;
      simpl in *; subst.
    unfold C_size_vars; simpl.
    apply Plus.plus_le_lt_compat; try lia.
    apply mul_S_same.
    repeat rewrite app_assoc.
    rewrite remove_dups_length_perm
      with (l := (tvars l1 ∪ tvars r1 ∪ tvars l2 ∪ tvars e2 ∪ Ctvars C')%set)
           (l' := (tvars l1 ∪ tvars l2 ∪ tvars r1 ∪ tvars e2 ∪ Ctvars C')%set);
      try lia.
    repeat apply Permutation_app_tail.
    repeat rewrite <- app_assoc.
    apply Permutation_app_head.
    apply Permutation_app_comm.
  - intros C p C' l r l1 l2 Heql R HeqR Heqp HeqC _ Hmem;
      simpl in *; subst.
    unfold C_size_vars; simpl.
    rewrite remove_dups_length_perm
      with (l := (tvars l1 ∪ tvars l2 ∪ (R :: Ctvars C'))%set)
           (l' := R :: (tvars l1 ∪ tvars l2 ∪ Ctvars C')%set); simpl.
    + repeat rewrite member_app_or in *.
      rewrite orb_false_iff in Hmem.
      destruct Hmem as [Hmem1 Hmem2].
      rewrite Hmem1, Hmem2; simpl.
      repeat rewrite app_length.
      pose proof In_member_reflects R (Ctvars C') as HRC'; inv HRC';
        unfold NatEqDec, nat_eq_eqdec in *; simpl.
      * rewrite <- H; simpl. admit.
      * rewrite <- H; simpl.
        rewrite Ctsub_not_in_tvars by auto.
        rewrite Ctsub_empty.
        repeat rewrite plus_n_Sm.
        rewrite Nat.add_comm
          with (n:=length (remove_dups (tvars l1 ∪ tvars l2 ∪ Ctvars C')%set)).
        rewrite <- Nat.add_assoc.
        apply Plus.plus_le_lt_compat; try lia.
        apply mul_S; auto using remove_dups_length_app_r.
    + apply Permutation_sym.
      apply Permutation_middle.
  - intros C p C' l r L Heql Heqp HeqC Hyp_eq Hmem;
      subst; simpl in *.
    unfold C_size_vars; simpl.
    repeat rewrite member_app_or.
    unfold NatEqDec, nat_eq_eqdec in *; simpl.
    rewrite Hmem; simpl.
    repeat rewrite app_length.
    pose proof In_member_reflects L (Ctvars C') as HLC'; inv HLC';
      unfold NatEqDec, nat_eq_eqdec in *; simpl.
    + rewrite <- H; simpl. admit.
    + rewrite <- H; simpl.
      rewrite Ctsub_not_in_tvars by auto.
      rewrite Ctsub_empty by auto.
      repeat rewrite plus_n_Sm.
      rewrite Nat.add_comm
        with (n := length (remove_dups (tvars r ∪ Ctvars C')%set)).
      rewrite <- Nat.add_assoc.
      apply Plus.plus_le_lt_compat; try lia.
      apply mul_S; auto using remove_dups_length_app_r.
Abort.
