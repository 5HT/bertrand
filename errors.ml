open Datatypes

exception Other of string
exception InvalidTermError of sexp
exception AlreadyDefinedError of string
exception ApplicationMismatch of string * int * int
exception ReplacingBoundWithConstant of string * term
exception ReplacingWithBound of string * sub
exception ReplacingBoundWith of string * string
exception UnificationError of term * term
exception ExpectedVariable of term
exception MatchError of term * term
exception AdmittedError
exception NotDefinedError of string
exception Parser of int * int
exception Lexer of string * int * int
exception Goals of term list

let prettyPrintError : exn -> unit = function
  | Other s -> print_endline s
  | ApplicationMismatch (name, v1, v2) ->
    Printf.printf "%s expects %d arguments, but got %d\n" name v1 v2
  | InvalidTermError x ->
    Printf.printf "Invalid term: %s\n" (showSExp x)
  | AlreadyDefinedError s ->
    Printf.printf "“%s” is already defined\n" s
  | ReplacingBoundWithConstant (name, omega) ->
    Printf.printf "Cannot replace bound variable “%s” with a constant “%s”\n"
      name (showTerm omega)
  | ReplacingWithBound (name, substs) ->
    Printf.printf "Replacing variable “%s” with a bound variable: %s.\n"
      name (showSub substs)
  | ReplacingBoundWith (a, b) ->
    Printf.printf "Replacing bound variable “%s” with a present in term variable “%s”.\n" a b
  | UnificationError (u, v) ->
    Printf.printf "“%s” cannot be unified with “%s”\n" (showTerm u) (showTerm v)
  | ExpectedVariable u ->
    Printf.printf "“%s” expected to be a variable\n" (showTerm u)
  | MatchError (u, v) ->
    Printf.printf "“%s” does not match “%s”\n" (showTerm u) (showTerm v)
  | AdmittedError -> print_endline "Admitted."
  | NotDefinedError s -> Printf.printf "“%s” is not defined\n" s
  | Parser (x, y) ->
    Printf.printf "Parsing error at %d:%d\n" x y
  | Lexer (msg, x, y) ->
    Printf.printf "Lexer error at %d:%d: %s\n" x y msg
  | Goals xs ->
    Printf.printf "There are open goals:\n";
    List.iter (fun tau -> Printf.printf "⊢ %s\n" (showTerm tau)) xs
  | Sys_error s -> print_endline s
  | ex -> Printf.printf "Uncaught exception: %s\n" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (default : 'b) (x : 'a) : 'b =
  try f x with ex -> prettyPrintError ex; default

let fail x = raise (Other x)