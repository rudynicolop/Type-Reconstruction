Require Export Coq.Classes.EquivDec.

Section Env.
  Context {K V : Set}.

  Definition env : Set := K -> option V.
  
  Context {HDK : EqDec K eq}.

  Definition bind (k : K) (v : V) (e : env) : env :=
    fun k' => if equiv_dec k' k then Some v else e k'.

  Definition find (k : K) (e : env) : option V := e k.
End Env.
