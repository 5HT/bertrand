open Sexp
open Lexing
open Errors
open Prelude
open Checker
open Datatypes

let parseErr f lexbuf =
  try f Lexer.main lexbuf with
  | Parser.Error ->
    raise (Errors.Parser (lexeme_start lexbuf, lexeme_end lexbuf))
  | Failure msg ->
    raise (Errors.Lexer (msg, lexeme_start lexbuf, lexeme_end lexbuf))

let parse filename =
  let chan = open_in filename in
  Printf.printf "Parsing “%s”.\n" filename;
  let lexbuf = Lexing.from_channel chan in
  parseErr Parser.file lexbuf

let sep = "─-"

(* This will probably be faster
   than converting string into char list
   and using List.for_all *)
let isSeparator : sexp -> bool = function
  | Atom s -> let res = ref true in
    String.iter (fun ch -> res := String.contains sep ch && !res) s; !res
  | _      -> false

let extList : sexp -> sexp list = function
  | List xs -> xs
  | u       -> showSExp u
               |> Printf.sprintf "Expected list at “%s”"
               |> fun x -> Other x
               |> raise

let rec macroexpand curr tau =
  let mu =
    findMap (fun (pattern, body) ->
              Option.bind (getMatch Sub.empty pattern tau)
                (fun substs -> Some (multisubst substs body))) curr.defs in

  match Option.value mu ~default:tau with
  | Symtree xs -> Symtree (List.map (macroexpand curr) xs)
  | v          -> v

let parseTerm curr expr =
  macroexpand curr (term curr expr)

let separators = [":="; "≔"]
let genSub curr xs =
  let rec genSubAux env : sexp list -> sub = function
    | x :: Atom sep :: value :: rest ->
      if List.mem sep separators then
        genSubAux (Sub.add (symbol x, -1) (parseTerm curr value) env) rest
      else
        Printf.sprintf "Substituion must have the form “α ≔ τ”: %s %s %s"
          (showSExp x) sep (showSExp value)
       |> fail
    | [] -> env
    | _ -> raise (Other "Invalid substitution list.") in
  genSubAux Sub.empty xs

let getSupp : sexp -> sexp list = function
  | Supp xs -> xs
  | expr    -> showSExp expr
               |> Printf.sprintf "Expected list in square brackets at “%s”."
               |> fail

let rec parseProof curr : sexp list -> (string * sub) list = function
  | Atom x :: Supp xs :: rest ->
    (x, genSub curr xs |> Sub.map freeze) :: parseProof curr rest
  | Atom x :: rest -> (x, Sub.empty) :: parseProof curr rest
  | [] -> []
  | xs -> showSExp (List xs)
          |> Printf.sprintf "Invalid proof: “%s”."
          |> fail

let preamble curr (expr : (sexp list) ref) =
  let finished : bool ref          = ref false in
  let expected : int ref           = ref 0 in
  let names    : (string list) ref = ref [] in
  let premises : (term list) ref   = ref [] in

  while List.length !expr > 0 && not !finished do
    let elem = pop expr in
    if isSeparator elem then begin
      names    := symbol (pop expr) :: !names;
      expected := !expected + 1
    end
    else if !expected <> 0 then begin
      premises := parseTerm curr elem :: !premises;
      expected := !expected - 1
    end
    else begin
      expr := elem :: !expr;
      finished := true
    end
  done;
  if List.length !names <> List.length !premises then
    raise (Other "Invalid theorem definition (number of premise names ≠ number of premises)")
  else ();

  let name = pop names in let conclusion = pop premises in
  (name, conclusion,
   List.rev !names, List.rev !premises,
   parseProof curr !expr)

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

let evalTheorem src =
  let (name, conclusion, names, premises, proof) = preamble !st (ref src) in
  let ctx = List.fold_left2 upTerm !st.context names premises in

  try
    check ctx !st.bound (freeze conclusion) proof;
    upDecl st name { premises = premises; conclusion = conclusion };
    Printf.printf "“%s” declared\n" name
  with ex ->
    Printf.printf "“%s” has not been declared\n" name;
    prettyPrintError ex

let rec elab : sexp list -> unit = function
  | [Atom "infix"; Atom op; Atom prec] ->
    st := { !st with infix = Env.add op (int_of_string prec) !st.infix }
  | Atom "variables" :: xs ->
    st := { !st with variables = !st.variables @ List.map symbol xs }
  | Atom "bound" :: xs ->
    st := { !st with bound = !st.bound @ List.map (term !st) xs }
  | [Atom "define"; pattern; body] ->
    st := { !st with defs = (term !st pattern, parseTerm !st body) :: !st.defs }
  | Atom "include" :: xs ->
    List.iter (symbol >> dofile) xs
  | Atom "macroexpand" :: xs ->
    List.iter (fun x ->
      showTerm (parseTerm !st x)
      |> Printf.printf "%s expands to %s\n" (showSExp x)) xs
  | Atom "postulate" :: expr ->
    let stack : (sexp list) ref = ref expr in
    let premises : (term list) ref = ref [] in
    while nonempty !stack do
      let x = pop stack in
      if isSeparator x then begin
        let name       = symbol (pop stack) in
        let conclusion = parseTerm !st (pop stack) in
        upDecl st name { premises = !premises; conclusion = conclusion };
        Printf.printf "“%s” postulated\n" name;
        premises := []
      end else premises := !premises @ [parseTerm !st x]
    done;
    if nonempty !premises then
      raise (Other "Incomplete postulate.")
    else ()
  | Atom "lemma"   :: expr
  | Atom "theorem" :: expr -> evalTheorem expr
  | x :: xs ->
    Other (Printf.sprintf "Unknown/incorrect form “%s”" (showSExp x)) |> raise
  | []      -> Other "Empty S-Expression" |> raise
and dofile filename =
  parse filename |> List.iter (extList >> handleErrors elab ())