type sexp =
| Atom of string
| Int of int
| List of sexp list
| Supp of sexp list

let rec showSExp : sexp -> string = function
  | Atom s  -> s
  | Int x   -> string_of_int x
  | List xs -> "(" ^ String.concat " " (List.map showSExp xs) ^ ")"
  | Supp xs -> "[" ^ String.concat " " (List.map showSExp xs) ^ "]"

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

type env = term Env.t

type argument =
  | Sorry of name
  | Lemma of name

type proof =
{ edge          : name;
  arguments     : argument list;
  substitutions : env }

type inferenceRule =
{ premises   : term list;
  conclusion : term }

type state =
{ variables : name list;
  infix     : int Env.t;
  context   : inferenceRule Env.t;
  bound     : term list;
  defs      : (term * term) list }