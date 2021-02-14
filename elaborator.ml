open Sexp
open Errors
open Parser
open Prelude
open Checker
open Datatypes

let st : state ref = ref
  { variables = [];
    infix     = Env.empty;
    context   = Env.empty;
    bound     = [];
    defs      = [] }

let upTerm ctx name tau =
  Env.add name { premises = []; conclusion = freeze tau } ctx

let upDecl st name decl =
  if Env.mem name !st.context then
    raise (AlreadyDefinedError name)
  else st := { !st with context = Env.add name decl !st.context }

let parse expr = Parser.parse !st expr

let rec elab : command -> unit = function
  | Infix (op, prec) ->
    st := { !st with infix = Env.add op prec !st.infix }
  | Variables xs ->
    st := { !st with variables = !st.variables @ xs }
  | Bound xs ->
    st := { !st with bound = !st.bound @ xs }
  | Macro (pattern, body) ->
    st := { !st with defs = (pattern, body) :: !st.defs }
  | Include xs -> List.iter dofile xs
  | Macroexpand xs ->
    List.iter (fun (x, y) ->
      Printf.printf "%s expands to %s\n" (showSExp x) (showTerm y)) xs
  | Axiom xs ->
    List.iter (fun (name, rule) ->
      upDecl st name rule;
      Printf.printf "“%s” postulated\n" name) xs
  | Decl { name; hypothesises; rule; proof } ->
    let ctx = List.fold_left2 upTerm !st.context hypothesises rule.premises in
    try
      check ctx !st.bound (freeze rule.conclusion) proof;
      upDecl st name rule; Printf.printf "“%s” declared\n" name
    with ex ->
      Printf.printf "“%s” has not been declared\n" name;
      prettyPrintError ex
and dofile filename =
  getSExp filename
  |> List.iter (handle (extList >> parse >> elab) ())