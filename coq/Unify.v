Set Warnings "-unused-pattern-matching-variable".
Require Export CoqRecon.EqDecInst CoqRecon.Typ Coq.funind.Recdef.
Require Import CoqRecon.Pair.

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
    Unify ((t → τ, t' → τ') :: C) σ.

Section ComputeUnify.

  Local Hint Unfold C_size_vars : core.
  Local Hint Resolve wf_lt_pair : core.
  Local Hint Resolve well_founded_inj : core.

  Open Scope set_scope.
  
  Function unify
           (C : list (typ * typ))
           {wf (fun C1 C2 => C_size_vars C1 ⊏ C_size_vars C2) C}
  : option tenv :=
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
        | l → l', r → r' =>
          unify ((l,r) :: (l',r') :: C)
        | _, _ => None
        end
    end.
  Proof.
    - intros C ? C' l r ? ? Heq; subst;
        autounfold with core; simpl.
      rewrite app_assoc.
      rewrite uniques_app.
      apply typ_eq_eq in Heq; subst.
      rewrite uniques_app_same.
      rewrite <- uniques_app.
      rewrite length_uniques_app.
      rewrite uniques_app_diff.
      rewrite app_length.
      destruct (length (uniques (tvars r) ∖ Ctvars C')%set)
        as [| len].
      + rewrite Nat.add_0_r. right.
        pose proof typ_size_non_zero r. lia.
      + left. lia.
    - intros ? ? C' ? ? ? R ? ? ? _ _;
        subst; autounfold with core; simpl.
      pose proof In_member_reflects R (Ctvars C') as HRC'; inv HRC'.
      + rewrite Ctsub_length_uniques_Ctvars by intuition; simpl.
        rewrite count_remove_length. rewrite app_nil_r.
        pose proof count_length_le (uniques (Ctvars C')) R.
        rewrite count_uniques_in in * by assumption.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        rewrite remove_uniques_comm.
        rewrite remove_not_in by assumption.
        left. lia.
    - intros ? ? C' ? ? ? R ? ? ? _ _;
        subst; autounfold with core; simpl.
      pose proof In_member_reflects R (Ctvars C') as HRC'; inv HRC'.
      + rewrite Ctsub_length_uniques_Ctvars by intuition; simpl.
        rewrite count_remove_length. rewrite app_nil_r.
        pose proof count_length_le (uniques (Ctvars C')) R.
        rewrite count_uniques_in in * by assumption.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        rewrite remove_uniques_comm.
        rewrite remove_not_in by assumption.
        left. lia.
    - intros ? ? C' ? ? l1 l2 ? r1 r2 ? ? ? Hteq;
        subst; autounfold with core; simpl in *.
      rewrite andb_false_iff in Hteq.
      repeat rewrite typ_eq_not_eq in Hteq.
      repeat rewrite app_assoc.
      assert (HP :
                Permutation
                  (tvars l1 ∪ tvars r1 ∪ tvars l2 ∪ tvars r2 ∪ Ctvars C')
                  (tvars l1 ∪ tvars l2 ∪ tvars r1 ∪ tvars r2 ∪ Ctvars C')).
      { repeat apply Permutation_app_tail.
        repeat rewrite <- app_assoc.
        apply Permutation_app_head.
        apply Permutation_app_swap. }
      apply uniques_perm in HP.
      apply Permutation_length in HP.
      unfold NatEqDec,nat_eq_eqdec in *.
      rewrite HP; clear HP. right. lia.
    - intros ? ? C' ? ? l1 l2 ? R ? ? ? _ Hmem;
        subst; autounfold with core; simpl in *.
      repeat rewrite Not_In_member_iff in Hmem.
      rewrite length_uniques_app with (r := R :: Ctvars C'); simpl.
      pose proof In_member_reflects R (Ctvars C') as HRC'; inv HRC'.
      + rewrite Ctsub_length_uniques_Ctvars by assumption; simpl.
        rewrite count_remove_length.
        pose proof count_length_le
             (uniques (Ctvars C' ∪ (tvars l1 ∪ tvars l2))) R.
        rewrite count_uniques_in in * by intuition.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        rewrite in_app_iff in Hmem.
        apply Decidable.not_or in Hmem as [Hmem1 Hmem2].
        rewrite remove_uniques_comm.
        repeat rewrite remove_app.
        repeat rewrite remove_not_in by intuition.
        repeat rewrite uniques_app_diff.
        left. repeat rewrite app_length. lia.
    - intros ? ? C' ? r L ? ? ? Hteq Hmem;
        subst; autounfold with core; simpl.
      pose proof In_member_reflects L (Ctvars C') as HRC'; inv HRC'.
      + rewrite Not_In_member_iff in Hmem.
        rewrite Ctsub_length_uniques_Ctvars by assumption.
        rewrite count_remove_length.
        pose proof count_length_le (uniques (Ctvars C' ∪ tvars r)) L.
        rewrite length_uniques_app with (l := Ctvars C') in *.
        rewrite count_uniques_in in * by intuition.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        rewrite remove_uniques_comm.
        rewrite remove_app.
        rewrite Not_In_member_iff in Hmem.
        rewrite (remove_not_in (tvars r)) by assumption.
        rewrite remove_not_in by assumption.
        rewrite length_uniques_app.
        pose proof length_uniques_app_le (Ctvars C') (tvars r).
        left. unfold "<".
        apply le_n_S. assumption.
    - intuition.
  Defined.
End ComputeUnify.
