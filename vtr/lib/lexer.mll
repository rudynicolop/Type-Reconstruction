{
	open Parser
}

let id = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9']*
let num = ['0'-'9']*
let whitespace = [' ' '\t' '\n']

rule tokenize = parse
| whitespace { tokenize lexbuf }
| "(" { LPAREN }
| ")" { RPAREN }
| "fun" { FUN }
| "." { DOT }
| "let" { LET }
| ":=" { ASS }
| "in" { IN }
| "&&" { AND }
| "||" { OR }
| "+" { ADD }
| "-" { SUB }
| "=" { EQ }
| "<" { LT }
| "true" { BOOL true }
| "false" { BOOL false }
| num as n { NAT (int_of_string n) }
| id as x { VAR x}