Set Warnings "-unused-pattern-matching-variable".
Require Export CoqRecon.Util.EqDecInst CoqRecon.Syntax.Typ Coq.funind.Recdef.
Require Import CoqRecon.Util.Pair.

Open Scope maybe_scope.
Open Scope set_scope.
Open Scope env_scope.

Inductive is_tvar : typ -> Prop :=
| is_tvar_intro (T : nat) : is_tvar T.

Inductive Unify : list (typ * typ) -> tenv -> Prop :=
| Unify_nil :
    Unify [] ∅
| Unify_cons_skip τ C σ :
    Unify C σ ->
    Unify ((τ,τ) :: C) σ
| Unify_cons_var_both_l L R C σ :
    L < R ->
    let s := L ↦ TVar R;; ∅ in
    Unify (Ctsub s C) σ ->
    Unify ((TVar L, TVar R) :: C) (σ ‡ s)
| Unify_cons_var_both_r L R C σ :
    R < L ->
    let s := R ↦ TVar L;; ∅ in
    Unify (Ctsub s C) σ ->
    Unify ((TVar L, TVar R) :: C) (σ ‡ s)
| Unify_cons_var_just_l T τ C σ :
    ~ is_tvar τ -> T ∉ tvars τ ->
    let s := T ↦ τ;; ∅ in
    Unify (Ctsub s C) σ ->
    Unify ((TVar T, τ) :: C) (σ ‡ s)
| Unify_cons_var_just_r τ T C σ :
    ~ is_tvar τ -> T ∉ tvars τ ->
    let s := T ↦ τ;; ∅ in
    Unify (Ctsub s C) σ ->
    Unify ((τ, TVar T) :: C) (σ ‡ s)
| Unify_cons_arrow t t' τ τ' C σ :
    t <> t' \/ τ <> τ' ->
    Unify ((t,t') :: (τ,τ') :: C) σ ->
    Unify ((t → τ, t' → τ') :: C) σ.

Section ComputeUnify.
  Local Hint Unfold C_size_vars : core.
  Local Hint Resolve wf_lt_pair : core.
  Local Hint Resolve well_founded_inj : core.
  
  Function unify
           (C : list (typ * typ))
           {wf (fun C1 C2 => C_size_vars C1 ⊏ C_size_vars C2) C}
  : option tenv :=
    match C with
    | []         => Some ∅
    | (l, r) :: C =>
      if typ_eq l r then
        unify C
      else
        match l, r with
        | TVar L, TVar R =>
          match lt_eq_lt_dec L R with
          | inleft (left _) =>
            let s' := L ↦ r;; ∅ in
            let! s := unify (Ctsub s' C) in s ‡ s'
          | inleft (right _) =>
            None
          | inright (_) =>
            let s' := R ↦ l;; ∅ in
            let! s := unify (Ctsub s' C) in s ‡ s'
          end
        | TVar L, _ =>
          if member L (tvars r) then
            None
          else
            let s' := L ↦ r;; ∅ in
            let! s := unify (Ctsub s' C) in s ‡ s'
        | _, TVar R =>
          if member R (tvars l) then
            None
          else
            let s' := R ↦ l;; ∅ in
            let! s := unify (Ctsub s' C) in s ‡ s'
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
    - intros ? ? C' ? ? L ? ? ? ? _ _;
        subst; autounfold with core; simpl.
      pose proof In_member_reflects L (Ctvars C') as HRC'; inv HRC'.
      + rewrite Ctsub_length_uniques_Ctvars by intuition; simpl.
        rewrite count_remove_length. rewrite app_nil_r.
        pose proof count_length_le (uniques (Ctvars C')) L.
        rewrite count_uniques_in in * by assumption.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        rewrite remove_uniques_comm.
        rewrite remove_not_in by assumption.
        left. lia.
    - intros ? ? C' ? ? L ? ? ? ? _ _;
        subst; autounfold with core; simpl.
      pose proof In_member_reflects L (Ctvars C') as HRC'; inv HRC'.
      + rewrite Ctsub_length_uniques_Ctvars by intuition; simpl.
        rewrite count_remove_length. rewrite app_nil_r.
        pose proof count_length_le (uniques (Ctvars C')) L.
        rewrite count_uniques_in in * by assumption.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        rewrite remove_uniques_comm.
        rewrite remove_not_in by assumption.
        left. lia.
    - intros ? ? C' ? ? L ? r1 r2 ? ? ? _ Hmem;
        subst; autounfold with core; simpl in *.
      repeat rewrite Not_In_member_iff in Hmem.
      pose proof In_member_reflects L (Ctvars C') as HRC'; inv HRC'.
      + rewrite Ctsub_length_uniques_Ctvars by assumption; simpl.
        rewrite count_remove_length.
        pose proof count_length_le
             (uniques (Ctvars C' ∪ (tvars r1 ∪ tvars r2))) L.
        rewrite count_uniques_in in * by intuition.
        rewrite length_uniques_app with (r := Ctvars C'); simpl.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        rewrite in_app_iff in Hmem.
        apply Decidable.not_or in Hmem as [Hmem1 Hmem2].
        rewrite remove_uniques_comm.
        repeat rewrite remove_app.
        repeat rewrite remove_not_in by intuition.
        rewrite length_uniques_app with (r := Ctvars C'); simpl.
        repeat rewrite uniques_app_diff.
        left. repeat rewrite app_length. lia.
    - intros ? ? C' ? ? L ? R ? ? ? Hteq ? HLR _ _;
        subst; autounfold with core; simpl; dispatch_eqdec; try lia.
      pose proof In_member_reflects L (Ctvars C') as HCL.
      pose proof In_member_reflects R (Ctvars C') as HCR.
      inv HCL; inv HCR.
      + rewrite Ctsub_length_uniques_Ctvars by firstorder lia. simpl.
        rewrite length_uniques_app; simpl.
        repeat rewrite count_remove_length.
        rewrite remove_uniques_comm.
        pose proof count_length_le (uniques (Ctvars C')) R.
        pose proof count_length_le (uniques (remove R (Ctvars C'))) L.
        repeat rewrite count_uniques_in in * by auto using remove_complete.
        left. lia.
      + rewrite Ctsub_length_uniques_Ctvars by firstorder lia. simpl.
        rewrite length_uniques_app; simpl.
        rewrite remove_not_in with (a := R) by auto using uniques_sound.
        rewrite count_remove_length.
        pose proof count_length_le (uniques (Ctvars C')) L.
        rewrite count_uniques_in in * by assumption.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty. rewrite remove_comm.
        rewrite remove_not_in with (a := L) by auto using uniques_sound.
        rewrite count_remove_length.
        pose proof count_length_le (uniques (Ctvars C')) R.
        rewrite count_uniques_in in * by assumption.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        repeat rewrite remove_not_in with (l := uniques (Ctvars C'))
          by auto using uniques_sound.
        left. lia.
    - intros ? ? C' ? ? L ? R ? ? ? Hteq HRL _;
        subst; autounfold with core; simpl; dispatch_eqdec; try lia.
      pose proof In_member_reflects L (Ctvars C') as HCL.
      pose proof In_member_reflects R (Ctvars C') as HCR.
      inv HCL; inv HCR.
      + rewrite Ctsub_length_uniques_Ctvars by firstorder lia. simpl.
        rewrite length_uniques_app; simpl.
        repeat rewrite count_remove_length.
        rewrite remove_uniques_comm.
        pose proof count_length_le (uniques (Ctvars C')) R.
        pose proof count_length_le (uniques (remove R (Ctvars C'))) L.
        repeat rewrite count_uniques_in in * by auto using remove_complete.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        rewrite remove_not_in with (a := R) by auto using uniques_sound.
        rewrite count_remove_length.
        pose proof count_length_le (uniques (Ctvars C')) L.
        rewrite count_uniques_in in * by assumption.
        left. lia.
      + rewrite Ctsub_length_uniques_Ctvars by firstorder lia. simpl.
        rewrite length_uniques_app; simpl. rewrite remove_comm.
        rewrite remove_not_in with (a := L) by auto using uniques_sound.
        rewrite count_remove_length.
        pose proof count_length_le (uniques (Ctvars C')) R.
        rewrite count_uniques_in in * by assumption.
        left. lia.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        repeat rewrite remove_not_in with (l := uniques (Ctvars C'))
          by auto using uniques_sound.
        left. lia.
    - intuition.
  Defined.
End ComputeUnify.
