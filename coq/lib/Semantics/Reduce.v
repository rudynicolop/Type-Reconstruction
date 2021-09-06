Require Export CoqRecon.Syntax.Term CoqRecon.Util.EqDecInst.

Reserved Notation "'⟦' x ':=' v '⟧' e"
         (at level 20, right associativity).

Open Scope term_scope.

(** Capture-avoiding Substitution. *)
Fixpoint sub (x : string) (v e : term) : term :=
  match e with
  | Var y   => if equiv_dec x y then v else y
  | λ y ⇒ e => if equiv_dec x y then λ y ⇒ e else λ y ⇒ ⟦x:=v⟧ e
  | e1 ⋅ e2 => ⟦x:=v⟧ e1 ⋅ ⟦x:=v⟧ e2
  | Bool b  => Bool b
  | Nat n   => Nat n
  | Cond e1 e2 e3 => Cond (⟦x:=v⟧ e1) (⟦x:=v⟧ e2) (⟦x:=v⟧ e3)
  | Op o e1 e2    => Op o (⟦x:=v⟧ e1) (⟦x:=v⟧ e2)
  | LET y e1 e2   => LET y (⟦x:=v⟧ e1) (if equiv_dec x y then e2 else ⟦x:=v⟧ e2)
  end
where "'⟦' x ':=' v '⟧' e" := (sub x v e).

Open Scope maybe_scope.
Open Scope op_scope.

(** Call-by-name Evaluation. *)
Fixpoint rd (e : term) : option term :=
  match e with
  | Var _ | λ _ ⇒ _ | Bool _ | Nat _ => None
  | (λ x ⇒ e1) ⋅ e2 => Some (⟦x:=e2⟧ e1)
  | e1 ⋅ e2 => let! e1' := rd e1 in e1' ⋅ e2
  | Cond true  e2 _ => Some e2
  | Cond false _ e3 => Some e3
  | Cond e1 e2 e3 => let! e1' := rd e1 in Cond e1' e2 e3
  | LET x e1 e2 => Some (⟦x:=e1⟧ e2)
  | Op ⨥ (Nat n1)  (Nat n2)  => Some (Nat  (n1 + n2))
  | Op ⨪ (Nat n1)  (Nat n2)  => Some (Nat  (n1 - n2))
  | Op ∧ (Bool b1) (Bool b2) => Some (Bool (b1 &&  b2))
  | Op ∨ (Bool b1) (Bool b2) => Some (Bool (b1 || b2))
  | Op ≅ (Nat n1)  (Nat n2)  => Some (Bool (n1 =? n2))
  | Op ≦ (Nat n1)  (Nat n2)  => Some (Bool (n1 <=? n2))
  | Op o ((Nat _ | Bool _) as e1) e2 =>
    let! e2' := rd e2 in Op o e1 e2'
  | Op o e1 e2 => let! e1' := rd e1 in Op o e1' e2
  end.

Inductive value : term -> Prop :=
| v_abs x e : value (λ x ⇒ e)
| v_nat (n : nat) : value n
| v_bool (b : bool) : value b.
