type name = string

type term =
| Lit of name
| Var of name
| Symtree of term list
| Hole

let rec showTerm : term -> string = function
  | Lit s -> s
  | Var s -> s
  | Symtree xs -> "(" ^ String.concat " " (List.map showTerm xs) ^ ")"
  | Hole -> "_"

module Env = Map.Make(String)

type derivation =
| Proof of proof
| Sorry of string
and proof =
{ edge          : name;
  children      : derivation list;
  substitutions : env }
and env = term Env.t

type inferenceRule =
{ premises   : term list;
  conclusion : term }

type state =
{ variables : name list;
  infix     : int Env.t;
  context   : inferenceRule Env.t;
  bound     : term list;
  defs      : (term * term) list }