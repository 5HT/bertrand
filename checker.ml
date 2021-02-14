open Datatypes
open Prelude
open Errors

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

let rec index idx = function
  | Lit x       -> Lit x
  | FVar (x, _) -> FVar (x, -1)
  | Var (x, _)  -> Var (x, idx)
  | Symtree xs  -> Symtree (List.map (index idx) xs)
  | Hole        -> Hole

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

let rec unify substs patt term =
  let err = MatchError (patt, term) in

  let omega = prune substs patt in
  let tau   = prune substs term in

  match omega, tau with
  | FVar a, FVar b when a = b -> substs
  | Var a, Var b when a = b -> substs
  | Var name, _ -> Sub.add name tau substs
  | _, Var name -> Sub.add name omega substs
  | Lit a, Lit b -> if a = b then substs else raise err
  | Symtree xs, Symtree ys ->
    if List.length xs <> List.length ys then raise err
    else List.fold_left2 unify substs xs ys
  | Hole, _ -> substs
  | _, _ -> raise err

let rec occurs tau name =
  match tau with
  | Var name'  -> name = name'
  | Lit _      -> false
  | Symtree xs -> List.exists (fun x -> occurs x name) xs
  | _          -> false

let even fi tau =
  if fi <> tau then raise (UnificationError (fi, tau))
  else ()

let lookup (ctx : rule Env.t) name =
  match Env.find_opt name ctx with
  | Some v -> v
  | _      -> raise (NotDefinedError name)

let rec findMap f = function
  | [] -> None
  | x :: l ->
    begin match f x with
      | Some _ as result -> result
      | None -> findMap f l
    end

let rec getBound (bound : term list) tau =
  let formula = findMap (fun x -> getMatch Sub.empty x tau) bound in
  let vars =
    begin match formula with
      | Some substs ->
        List.map
          (function
          | _, FVar name
          | _, Var name -> name
          | _, omega    -> raise (ExpectedVariable omega))
          (Sub.bindings substs)
      | None -> []
    end in
  match tau with
  | Symtree xs -> vars @ List.concat (List.map (getBound bound) xs)
  | _          -> vars

let rec hasVar (x : name) : term -> bool = function
  | FVar y | Var y -> x = y
  | Symtree xs     -> List.exists (hasVar x) xs
  | _              -> false

let checkSubst (bound : term list) (substs : sub) tau =
  let bvars = ref (getBound bound tau) in
  Sub.iter (fun name omega ->
    match omega with
    | FVar name' | Var name' when hasVar name tau ->
      (* Variable cannot be replaced with bound variable *)
      if List.mem name' !bvars then
        ReplacingWithBound (fst name, substs)
        |> raise
      else ();

      (* Bound variable cannot be replaced with present in term variable *)
      if List.mem name !bvars then
        if hasVar name' tau then
          ReplacingBoundWith (fst name, fst name')
          |> raise
        else bvars := name' :: !bvars
      else ()
    | _ ->
      (* Bound variable cannot be replaced with a constant *)
      if List.mem name !bvars then
        raise (ReplacingBoundWithConstant (fst name, omega))
      else ())
    substs

let substitute bound substs tau =
  checkSubst bound substs tau;
  multisubst substs tau

let synth ctx bound tau xs =
  let goals : (term list) ref = ref [tau] in
  let rwr   : sub ref = ref Sub.empty in

  List.iteri (fun idx (name, substs) ->
    let rule = lookup ctx name in
    let conclusion = index idx rule.conclusion in
    let premises = List.map (index idx) rule.premises in
    Sub.iter (fun (name, _) tau -> rwr := Sub.add (name, idx) tau !rwr) substs;

    let goal = pop goals in
    let expected = substitute bound !rwr conclusion in
    let unifying = unify Sub.empty expected goal in
    Sub.iter (fun k v -> rwr := Sub.add k v !rwr) unifying;
    rwr := Sub.map (substitute bound !rwr) !rwr;

    goals := premises @ !goals;
    goals := List.map (substitute bound !rwr) !goals) xs;

  if List.length !goals > 0 then
    raise (Goals !goals)
  else !rwr

let check ctx bound tau xs =
  let goals : (term list) ref = ref [tau] in
  let rwr = synth ctx bound tau xs in

  List.iteri (fun idx (name, _) ->
    let rule       = lookup ctx name in
    let conclusion = substitute bound rwr (index idx rule.conclusion) in
    let premises   = List.map (index idx >> substitute bound rwr) rule.premises in

    let goal = pop goals in
    even goal conclusion;

    goals := premises @ !goals) xs