Require Export Coq.Program.Utils Coq.Program.Basics.

Section Maybe.
  Context {A B : Type}.

  Definition obind (f : A -> option B) (o : option A) : option B :=
    match o with
    | Some a => f a
    | None => None
    end.

  Definition omap (f : A -> B) : option A -> option B :=
    obind (Some ∘ f)%prg.
End Maybe.

Declare Scope maybe_scope.
Delimit Scope maybe_scope with maybe.

Notation "o '>>=' f"
  := (obind f o)
       (at level 50, left associativity) : maybe_scope.
Notation "o '>>|' f"
  := (omap f o)
       (at level 50, left associativity) : maybe_scope.
Notation "a '<-' o ';;' b"
  := (obind (fun a => b) o)
       (at level 60, right associativity) : maybe_scope.
Notation "a '↤' o ';;' b"
  := (omap (fun a => b) o)
       (at level 60, right associativity) : maybe_scope.

Ltac maybe_simpl :=
  unfold ">>|","∘",">>=",omap,obind; simpl.

Ltac maybe_simpl_hyp H :=
  unfold ">>|","∘",">>=",omap,obind in H; simpl H.
