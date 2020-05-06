open Sexp
open Errors
open Lexing
open Prelude
open Checker
open Datatypes

let sep = "─-"

let extList : sexp -> sexp list = function
  | List xs -> xs
  | u       -> showSExp u
               |> Printf.sprintf "Expected list at “%s”"
               |> fun x -> Other x
               |> raise

(* This will probably be faster
   than converting string into char list
   and using List.for_all *)
let isSeparator : sexp -> bool = function
  | Atom s -> let res = ref true in
    String.iter (fun ch -> res := String.contains sep ch && !res) s; !res
  | _      -> false

let rec macroexpand curr tau =
  let mu =
    findMap (fun x -> let (pattern, body) = x in
                      try let substs = matches Env.empty pattern tau in
                          Some (multisubst substs body)
                      with MatchError _ -> None) curr.defs in
  let tau' = match mu with
  | Some v -> v
  | None   -> tau in
  match tau' with
  | Symtree xs -> Symtree (List.map (macroexpand curr) xs)
  | v          -> v

let parseTerm curr expr =
  macroexpand curr (term curr expr)

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

let init : state =
  { variables = [];
    infix     = Env.empty;
    context   = Env.empty;
    bound     = [];
    defs      = [] }

let st : state ref = ref init

let rec eval : sexp list -> unit = function
  | [Atom "infix"; Atom op; Int prec] ->
    st := { !st with infix = Env.add op prec !st.infix }
  | Atom "variables" :: xs ->
    st := { !st with variables = !st.variables @ List.map symbol xs }
  | Atom "bound" :: xs ->
    st := { !st with bound = !st.bound @ List.map (term !st) xs }
  | [Atom "define"; pattern; body] ->
    st := { !st with defs = (term !st pattern, parseTerm !st body) :: !st.defs }
  | Atom "include" :: xs ->
    List.iter (symbol >> dofile) xs
  | Atom "postulate" :: expr ->
    let stack : (sexp list) ref = ref expr in
    let premises : (term list) ref = ref [] in
    while nonempty !stack do
      match !stack with
      | x :: xs ->
        if isSeparator x then
          match xs with
          | top :: conclusion :: stack' ->
            let name = symbol top in
            if Env.mem name !st.context then
              raise (AlreadyDefinedError name)
            else
              st := { !st with context =
                      Env.add name
                        { premises   = !premises;
                          conclusion = parseTerm !st conclusion }
                        !st.context };
              stack := stack'; premises := []
          | _ -> raise (Other "Not enough arguments for postulate.")
        else premises := !premises @ [parseTerm !st x]
      | [] -> ()
    done;
    if nonempty !premises then
      raise (Other "Incomplete postulate.")
    else ()
  | x :: xs ->
    Other (Printf.sprintf "Unknown/incorrect form “%s”" (showSExp x)) |> raise
  | []      -> Other "Empty S-Expression" |> raise
and dofile filename =
  parse filename |> List.iter (extList >> eval)

let () =
  Array.to_list Sys.argv
  |> List.tl
  |> List.iter (handleErrors dofile ())