open Prelude

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
| Lit     of string
| FVar    of name
| Var     of name
| Symtree of term list
| Hole

let rec showTerm : term -> string = function
  | Lit s                   -> s
  | FVar (s, _)             -> s
  | Var  (s, _)             -> s
  | Symtree (Lit "@" :: xs) -> "[" ^ String.concat " " (List.map showTerm xs) ^ "]"
  | Symtree xs              -> "(" ^ String.concat " " (List.map showTerm xs) ^ ")"
  | Hole                    -> "_"

let rec showTermIdx : term -> string = function
  | Lit s         -> s
  | FVar (s, idx) -> Printf.sprintf "{%s}[%d]" s idx
  | Var  (s, idx) -> Printf.sprintf "%s[%d]" s idx
  | Symtree xs    -> "(" ^ String.concat " " (List.map showTermIdx xs) ^ ")"
  | Hole          -> "_"

let rec freeze = function
  | Lit x      -> Lit x
  | FVar x     -> FVar x
  | Var x      -> FVar x
  | Symtree xs -> Symtree (List.map freeze xs)
  | Hole       -> Hole

let rec subst name mu tau =
    match tau with
    | Var name'  -> if name = name' then mu else tau
    | Symtree xs -> Symtree (List.map (subst name mu) xs)
    | _          -> tau

module Variables = Set.Make(Name)

module Sub = Map.Make(Name)
type sub = term Sub.t

let showSub (substs : sub) =
  Sub.bindings substs
  |> List.map (fun ((name, idx), term) ->
    Printf.sprintf "%s[%d] -> %s" name idx (showTermIdx term))
  |> String.concat ", "

(* Performs simultaneous substituions *)
let multisubst substs tau =
  let salt = gensym () in
     Sub.fold (fun (name, idx) _  -> subst (name, idx) (Var (name ^ salt, idx))) substs tau
  |> Sub.fold (fun (name, idx) mu -> subst (name ^ salt, idx) mu) substs
  |> Sub.fold (fun (name, idx) _  -> subst (name ^ salt, idx) (Var (name, idx))) substs

let prune substs tau : term =
  match tau with
  | Var name -> Option.value (Sub.find_opt name substs) ~default:tau
  | _        -> tau

let lift3 (f : 'a -> 'b -> 'c -> 'd) (x : 'a option) : 'b -> 'c -> 'd =
  fun b c -> Option.bind x (fun a -> f a b c)

let rec getMatch substs patt tau =
  match prune substs patt, tau with
  | Var name, _ -> Some (Sub.add name tau substs)
  | Lit a, Lit b -> if a = b then Some substs else None
  | Symtree xs, Symtree ys ->
    if List.length xs <> List.length ys then None
    else List.fold_left2 (lift3 getMatch) (Some substs) xs ys
  | Hole, _ -> Some substs
  | _, _ -> None

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