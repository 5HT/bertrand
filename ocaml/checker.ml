open Datatypes
open Prelude
open Errors

let rec subst name mu tau =
  match tau with
  | Lit _ -> tau
  | Var name' -> if name = name' then mu else tau
  | Symtree xs -> Symtree (List.map (subst name mu) xs)
  | Hole -> tau

let multisubst substs tau =
  let salt = gensym () in
  Env.fold    (fun name _  -> subst name (Var (name ^ salt))) substs tau
  |> Env.fold (fun name mu -> subst (name ^ salt) mu) substs
  |> Env.fold (fun name _  -> subst (name ^ salt) (Var name)) substs

let prune substs tau =
  match tau with
  | Var name ->
    if Env.mem name substs then
      Env.find name substs
    else tau
  | _ -> tau

let rec matches substs patt tau =
  let err = MatchError (patt, tau) in
  let omega = prune substs patt in
  match omega, tau with
  | Var name, _ -> Env.add name tau substs
  | Lit a, Lit b -> if a = b then substs else raise err
  | Symtree xs, Symtree ys ->
    if List.length xs <> List.length ys then raise err
    else List.fold_left2 matches substs xs ys
  | Hole, _ -> substs
  | _, _ -> raise err

let itMatches substs patt tau =
  try ignore (matches substs patt tau); true
  with MatchError _ -> false

let getMatch substs patt tau =
  try Some (matches substs patt tau);
  with MatchError _ -> None

let rec occurs tau name =
  match tau with
  | Var name'  -> name = name'
  | Lit _      -> false
  | Symtree xs -> List.exists (fun x -> occurs x name) xs
  | _          -> false

let even fi tau =
  if fi <> tau then raise (UnificationError (fi, tau))
  else ()

let lookup (ctx : inferenceRule Env.t) name =
  match Env.find_opt name ctx with
  | Some v -> v
  | _      -> raise (NotDefinedError name)

(* Compatibility with OCaml 4.05
   From: https://github.com/ocaml/ocaml/blob/trunk/stdlib/list.ml *)
let rec findMap f = function
  | [] -> None
  | x :: l ->
    begin match f x with
      | Some _ as result -> result
      | None -> findMap f l
    end

let rec getBound (bound : term list) tau =
  let formula = findMap (fun x -> getMatch Env.empty x tau) bound in
  let vars =
    begin match formula with
      | Some substs ->
        List.map
          (function
          | _, Var name -> name
          | _, omega    -> raise (ExpectedVariable omega))
          (Env.bindings substs)
      | None -> []
    end in
  match tau with
  | Symtree xs -> vars @ List.concat (List.map (getBound bound) xs)
  | _          -> vars

let isVar : term -> bool = function
  | Var _ -> true
  | _     -> false

let checkSubst (bound : term list) (substs : env) tau =
  let vars = getBound bound tau in
  Env.iter (fun name omega ->
    if List.mem name vars && not (isVar omega) then
      raise (ReplacingBoundWithConstant (name, omega))
    else match omega with
    | Var name' ->
      if List.mem name' vars then
        raise (ReplacingWithBound (name, name'))
      else ()
    | _ -> ())
    substs

let sorry tree tau =
  match tree with
  | Sorry name -> Printf.printf "%s: expected “%s”" name (showTerm tau)
  | _          -> ()

let rec infer (ctx : inferenceRule Env.t) bound tree =
  let statement = lookup ctx tree.edge in
  let v1 = List.length tree.children in
  let v2 = List.length statement.premises in
  if v1 <> v2 then raise (ApplicationMismatch (tree.edge, v1, v2)) else ();
  List.iter2 (fun premise child ->
    checkSubst bound tree.substitutions premise;
    let expected = multisubst tree.substitutions premise in
    match child with
    | Sorry _ -> sorry child expected
    | Proof x -> infer ctx bound x |> even expected)
    statement.premises tree.children;
  checkSubst bound tree.substitutions statement.conclusion;
  multisubst tree.substitutions statement.conclusion

let check ctx bound tau : derivation -> unit = function
  | Sorry x -> sorry (Sorry x) tau
  | Proof x -> even (infer ctx bound x) tau