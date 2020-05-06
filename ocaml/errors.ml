open Datatypes

exception Other of string
exception InvalidTermError of sexp
exception AlreadyDefinedError of name
exception ApplicationMismatch of name * int * int
exception ReplacingBoundWithConstant of name * term
exception ReplacingWithBound of name * name
exception UnificationError of term * term
exception ExpectedVariable of term
exception MatchError of term * term
exception AdmittedError
exception NotDefinedError of name
exception Parser of int * int
exception Lexer of string * int * int

let prettyPrintError : exn -> unit = function
  | Other s -> print_endline s
  | ApplicationMismatch (name, v1, v2) ->
    Printf.printf "%s expects %d arguments, but got %d\n" name v1 v2
  | InvalidTermError x ->
    Printf.printf "Invalid term: %s" (showSExp x)
  | AlreadyDefinedError s ->
    Printf.printf "“%s” is already defined\n" s
  | ReplacingBoundWithConstant (name, omega) ->
    Printf.printf "Cannot replace bound variable “%s” with a constant “%s”\n"
      name (showTerm omega)
  | ReplacingWithBound (a, b) ->
    Printf.printf "Cannot replace “%s” with “%s”, because “%s” is bound\n" a b b
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
  | Sys_error s -> print_endline s
  | ex -> Printf.printf "Uncaught exception: %s\n" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (default : 'b) (x : 'a) : 'b =
  try f x with ex -> prettyPrintError ex; default