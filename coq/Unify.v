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
      + admit.
      + rewrite Ctsub_not_in_tvars by assumption.
        rewrite Ctsub_empty.
        rewrite remove_uniques_comm.
        rewrite remove_not_in by assumption.
        left. lia.
    - admit.
    - admit.
    - admit.
    - intros ? ? C' ? r L ? ? ? Hteq Hmem;
        subst; autounfold with core; simpl. admit.
    - Check wf_lt_pair. admit.
  Abort.
End ComputeUnify.
