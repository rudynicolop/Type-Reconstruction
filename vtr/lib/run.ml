open Coqrecon__Env
open Coqrecon__Typ
open Coqrecon__Term
open Coqrecon__Computes
open Coqrecon__Unify
open Coqrecon__Reduce
open ToString
open Core
open Option

let parse (filename : string) : term =
  filename
  |> Stdlib.open_in
  |> Lexing.from_channel
  |> Parser.prog Lexer.tokenize

let types (e : term) : (typ,string) Result.t =
  match cgen [] [] empty e with
  | None -> Result.Error "Program fails to type :("
  | Some ((t,_),c) ->
    begin match unify c with
      | None   -> Result.Error "Unable to unify constraints :("
      | Some s ->
        t
        |> tsub s
        |> Result.return
    end

let rec exec (e : term) : term option =
  e
  |> string_of_term
  |> (^) " -> "
  |> print_endline;
  eval e >>= exec

let pipeline (filename : string) (run : bool) : unit =
  let e = parse filename in
  string_of_term e
  |> (^) "Program parsed as:\n"
  |> print_endline;
  match types e with
  | Ok t ->
    t
    |> string_of_typ
    |> (^) "Program has type:\n"
    |> print_endline;
    if run then
      begin
        print_endline "Execution:";
        e
        |> exec
        |> ignore
      end
    else
      ()
  | Error msg ->
    msg
    |> (^) "Error: "
    |> print_endline
