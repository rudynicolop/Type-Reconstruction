open Coqrecon__Env
open Coqrecon__Typ
open Coqrecon__Term
open Coqrecon__Computes
open Coqrecon__Unify
open Coqrecon__Reduce
open ToString
open Core
open Option

let types (e : term) : unit =
  match cgen [] [] empty e with
  | None -> print_endline "Program fails to type :("
  | Some ((t,_),c) ->
    begin match unify c with
      | None   -> print_endline "Unable to unify constraints :("
      | Some s ->
        t
        |> tsub s
        |> string_of_typ
        |> (^) "Program has type:\n"
        |> print_endline
    end

let rec exec (e : term) : term option =
  e
  |> string_of_term
  |> (^) " -> "
  |> print_endline;
  eval e >>= exec
