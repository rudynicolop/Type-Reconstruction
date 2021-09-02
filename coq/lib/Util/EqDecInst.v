Require Export Coq.Strings.String Coq.Arith.PeanoNat Coq.Classes.EquivDec.

Instance StringEqDec : EqDec string eq := {equiv_dec := string_dec}.
Instance NatEqDec
  : @EqDec nat (@eq nat) (@eq_equivalence nat) :=
  {equiv_dec := Nat.eq_dec}.
