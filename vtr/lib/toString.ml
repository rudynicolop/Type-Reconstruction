open Coqrecon__Typ
open Coqrecon__Term

let rec string_of_typ (t : typ) : string =
  match t with
  | TArrow (t1,t2) ->
    "(" ^ string_of_typ t1 ^ "→" ^ string_of_typ t2 ^ ")"
  | TNat   -> "ℕ"
  | TBool  -> "𝔹"
  | TVar n -> "X" ^ Z.to_string n

let string_of_op (o : op) : string =
  match o with
  | And -> "&&"
  | Or  -> "||"
  | Add -> "+"
  | Sub -> "-"
  | Eq  -> "="
  | Lt  -> "<"

let rec string_of_term (e : term) : string =
  match e with
  | Var x     -> x
  | Abs (x,e) ->
    "(λ" ^ x ^ "." ^ string_of_term e ^ ")"
  | App (e1,e2) ->
    "(" ^ string_of_term e1 ^ " " ^ string_of_term e2 ^ ")"
  | Nat  n -> Z.to_string n
  | Bool b -> string_of_bool b
  | Cond (e1,e2,e3) ->
    "(if " ^ string_of_term e1 ^
    " then " ^ string_of_term e2 ^
    " else " ^ string_of_term e3 ^ ")"
  | Op(o,e1,e2) ->
    "(" ^ string_of_term e1 ^
    " " ^ string_of_op o ^
    " " ^ string_of_term e2 ^ ")"
  | LetIn(x,e1,e2) ->
    "(let " ^ x ^ " := " ^ string_of_term e1 ^
    " in " ^ string_of_term e2 ^ ")"
