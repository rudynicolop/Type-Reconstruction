From Coq Require extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNativeString.

(** Extraction of [nat] to [Zarith]'s [Z.t]. *)
Extract Inductive nat => "Z.t" ["Z.zero" "Z.succ"].

Extract Inlined Constant plus => "Z.add".
Extract Inlined Constant mult => "Z.mul".
Extract Inlined Constant pred => "(fun n -> Z.max Z.zero (Z.pred n))".
Extract Inlined Constant minus => "(fun n m -> Z.max Z.zero (Z.sub n m))".
Extract Inlined Constant max => "Z.max".
Extract Inlined Constant min => "Z.min".

Extract Inlined Constant EqNat.beq_nat => "Z.equal".
Extract Inlined Constant EqNat.eq_nat_decide => "Z.equal".
Extract Inlined Constant Peano_dec.eq_nat_dec => "Z.equal".

Extract Inlined Constant Compare_dec.leb => "Z.leq".
Extract Inlined Constant Compare_dec.le_lt_dec => "Z.leq".
Extract Inlined Constant Compare_dec.lt_eq_lt_dec =>
"(fun n m -> if Z.lt n m then Some true else if Z.equal n m then Some false else None)".

Require CoqRecon.Util.Base
        CoqRecon.Util.EqDecInst CoqRecon.Util.ListLib
        CoqRecon.Util.Sets CoqRecon.Util.Env
        CoqRecon.Util.Maybe CoqRecon.Util.Pair
        CoqRecon.Syntax.Typ CoqRecon.Syntax.Term
        CoqRecon.Semantics.TypEnv
        CoqRecon.Semantics.Reduce
        CoqRecon.Mono.Computes
        CoqRecon.Unify.Unify.

Separate Extraction CoqRecon.Util.Base
         CoqRecon.Util.EqDecInst CoqRecon.Util.ListLib
         CoqRecon.Util.Sets CoqRecon.Util.Env
         CoqRecon.Util.Maybe CoqRecon.Util.Pair
         CoqRecon.Syntax.Typ CoqRecon.Syntax.Term
         CoqRecon.Semantics.TypEnv
         CoqRecon.Semantics.Reduce
         CoqRecon.Mono.Computes
         CoqRecon.Unify.Unify.
