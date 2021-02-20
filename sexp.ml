open Errors
open Datatypes

let operator out stack =
  match !stack, !out with
  | f :: stack', x :: y :: out' ->
    stack := stack';
    out := Symtree [x; f; y] :: out'
  | _ -> raise (Other "Invalid application of binary operator")

let nonempty : 'a list -> bool = function
  | [] -> false
  | _  -> true

let isAtom : sexp -> bool = function
  | Atom _ -> true
  | _      -> false

let symbol : sexp -> string = function
  | Atom s -> s
  | _      -> raise (Other "Expected atom")

(* From: https://rosettacode.org/wiki/Parsing/Shunting-yard_algorithm#OCaml *)
let splitWhile p =
  let rec go ls xs =
    match xs with
    | x :: xs' when p x -> go (x :: ls) xs'
    | _ -> List.rev ls, xs
  in go []

let rec term curr expr =
  match expr with
  | List (Atom "#" :: xs) -> shuntingyard curr xs
  | List xs -> Symtree (List.map (term curr) xs)
  | Supp xs -> Symtree (Lit "@" :: List.map (term curr) xs)
  | Atom "_" -> Hole
  | Atom name ->
    if Names.mem name curr.variables then
      Var (name, -1)
    else Lit name
and shuntingyard curr exprs =
  let prec x =
    match x with
    | Atom op -> Env.find op curr.infix
    | _       -> raise (Other "Shunting-yard failed") in
  let rec pusher stack queue xs =
    match xs with
    | [] -> List.rev queue @ stack
    | Atom op :: rest when Env.mem op curr.infix ->
      let mv, stack' = splitWhile (fun op' -> prec (Atom op) < prec op') stack in
      pusher (Atom op :: stack') (mv @ queue) rest
    | x :: rest ->
      pusher stack (x :: queue) rest in
  let rec constr (stack : term list) (xs : sexp list) =
    match xs with
    | [] -> stack
    | Atom op :: rest when Env.mem op curr.infix ->
      begin match stack with
        | x :: y :: stack' ->
          constr (Symtree [y; Lit op; x] :: stack') rest
        | _ -> Other (Printf.sprintf "Not enough arguments for “%s”" op) |> raise
      end
    | x :: rest -> constr (term curr x :: stack) rest in
  match constr [] (pusher [] [] exprs) with
  | [res] -> res
  | _     ->
    let src = showSExp (List exprs) in
    Other (Printf.sprintf "Redundant arguments in “%s”" src) |> raise