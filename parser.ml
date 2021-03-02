open Sexp
open Errors
open Lexing
open Prelude
open Datatypes

let parseErr f lexbuf =
  try f Lexer.main lexbuf with
  | Reader.Error ->
    raise (Errors.Parser (lexeme_start lexbuf, lexeme_end lexbuf))
  | Failure msg ->
    raise (Errors.Lexer (msg, lexeme_start lexbuf, lexeme_end lexbuf))

let getSExp filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  parseErr Reader.file lexbuf

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

let expand curr tau =
  findMap (fun (pattern, body) ->
            (fun substs -> Some (multisubst substs body))
            |> Option.bind (getMatch Sub.empty pattern tau)) curr.defs

let rec macroexpand curr tau =
  match Option.value (expand curr tau) ~default:tau with
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

type command =
  | Infix       of string * int
  | Variables   of string list
  | Constants   of string list
  | Bound       of term list
  | Macro       of term * term
  | Include     of string list
  | Macroexpand of (sexp * term) list
  | Axiom       of (string * rule) list
  | Decl        of { name : string; hypothesises : string list;
                     rule : rule;   proof : (string * sub) list }
  | Description of (string * string) list

let parse curr : sexp list -> command = function
  | [Atom "infix"; Atom op; Atom prec] ->
    Infix (op, int_of_string prec)
  | Atom "variables" :: xs ->
    Variables (List.map symbol xs)
  | Atom "description" :: xs ->
    Description (oddEvenMap symbol (expandSExp >> List.map showSExp >> String.concat " ") xs)
  | Atom "constants" :: xs ->
    Constants (List.map symbol xs)
  | Atom "bound" :: xs ->
    Bound (List.map (term curr) xs)
  | [Atom "define"; pattern; body] ->
    Macro (term curr pattern, parseTerm curr body)
  | Atom "include" :: xs ->
    Include (List.map symbol xs)
  | Atom "macroexpand" :: xs ->
    Macroexpand (List.map (fun x -> (x, parseTerm curr x)) xs)
  | Atom "axiom"     :: expr
  | Atom "postulate" :: expr ->
    let res = ref [] in

    let stack : (sexp list) ref = ref expr in
    let premises : (term list) ref = ref [] in
    while nonempty !stack do
      let x = pop stack in
      if isSeparator x then begin
        let name       = symbol (pop stack) in
        let conclusion = parseTerm curr (pop stack) in
        res := (name, { premises = List.rev !premises;
                        conclusion = conclusion }) :: !res;
        premises := []
      end else premises := parseTerm curr x :: !premises
    done;
    if nonempty !premises then
      raise (Other "Incomplete postulate.")
    else Axiom (List.rev !res)
  | Atom "lemma"   :: expr
  | Atom "theorem" :: expr ->
    let (name, conclusion, names, premises, proof) = preamble curr (ref expr) in
    Decl { name = name; hypothesises = names; proof = proof;
           rule = { premises = premises; conclusion = conclusion } }
  | x :: xs ->
    Other (Printf.sprintf "Unknown/incorrect form “%s”" (showSExp x)) |> raise
  | []      -> Other "Empty S-Expression" |> raise
