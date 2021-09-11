%{
    open Coqrecon__Term
%}

(** Tokens. *)
%token LPAREN RPAREN EOF
%token AND OR ADD SUB EQ LT
%token FUN DOT LET IN ASS
%token <string> VAR
%token <int> NAT
%token <bool> BOOL

(** Start symbol. *)
%start <term> prog

(** Type annotations. *)
%type <term> let_term
%type <term> fun_term
%type <term> or_term
%type <term> and_term
%type <term> comp_term
%type <term> nat_term
%type <term> app_term
%type <term> var_term

%%

prog:
  | e=let_term EOF { e }

let_term:
  | LET x ASS e1=fun_term IN e2=let_term { LetIn(x,e1,e2) }
  | e=fun_term { e }

fun_term:
  | FUN x DOT e { Abs(x,e) }
  | e=or_term { e }

or_term:
  | e1=and_term OR e2=or_term { Op(Or,e1,e2) }
  | e=and_term { e }

and_term:
  | e1=comp_term AND e2=and_term { Op(And,e1,e2) }
  | e=comp_term { e }

comp_term:
  | e1=nat_term EQ e2=nat_term { Op(Eq,e1,e2) }
  | e1=nat_term LT e2=nat_term { Op(Lt,e1,e2) }

nat_term:
  | e1=nat_term ADD e2=var_term { Op(Add,e1,e2) }
  | e1=nat_term SUB e2=var_term { Op(Sub,e1,e2) }

var_term:
  | x=VAR { Var x }
  | n=NAT { Nat n }
  | b=BOOL { Bool b }
