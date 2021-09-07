open Coqrecon__Env
(* open Coqrecon__Typ *)
open Coqrecon__Term
open Coqrecon__Computes
open Coqrecon__Unify
(* open Coqrecon__Reduce *)

let types (e : term) : bool =
  match cgen [] [] empty e with
  | None -> false
  | Some (_,c) ->
    begin match unify c with
      | None -> false
      | Some _ -> true
    end
