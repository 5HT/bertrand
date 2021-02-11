type sexp =
| Atom of string
| List of sexp list
| Supp of sexp list

let rec showSExp : sexp -> string = function
  | Atom s  -> s
  | List xs -> "(" ^ String.concat " " (List.map showSExp xs) ^ ")"
  | Supp xs -> "[" ^ String.concat " " (List.map showSExp xs) ^ "]"

type name = string * int

module Name = struct
  type t = name
  let compare (xs, x) (ys, y) =
    match String.compare xs ys with
    | 0 -> Int.compare x y
    | v -> v
end

type term =
| Lit of string
| Var of name
| Symtree of term list
| Hole

let rec showTerm : term -> string = function
  | Lit s      -> s
  | Var (s, _) -> s
  | Symtree xs -> "(" ^ String.concat " " (List.map showTerm xs) ^ ")"
  | Hole       -> "_"

let rec showTermIdx : term -> string = function
  | Lit s        -> s
  | Var (s, idx) -> Printf.sprintf "%s[%d]" s idx
  | Symtree xs   -> "(" ^ String.concat " " (List.map showTermIdx xs) ^ ")"
  | Hole         -> "_"

module Sub = Map.Make(Name)
type sub = term Sub.t

let showSub (substs : sub) =
  Sub.bindings substs
  |> List.map (fun ((name, idx), term) ->
    Printf.sprintf "%s[%d] -> %s" name idx (showTermIdx term))
  |> String.concat ", "

module Env = Map.Make(String)
type env = term Env.t

type rule =
{ premises   : term list;
  conclusion : term }

type state =
{ variables : string list;
  infix     : int Env.t;
  context   : rule Env.t;
  bound     : term list;
  defs      : (term * term) list }