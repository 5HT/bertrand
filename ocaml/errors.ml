open Datatypes

exception VerificationError of string
exception AlreadyDefinedError of name
exception ApplicationMismatch of name * int * int
exception ReplacingBoundWithConstant of name * term
exception ReplacingWithBound of name * name
exception UnificationError of term * term
exception ExpectedVariable of term
exception MatchError of term * term
exception AdmittedError
exception NotDefinedError of name

let prettyPrintError : exn -> unit = function
  | VerificationError s -> print_endline s
  | ApplicationMismatch (name, v1, v2) ->
    Printf.printf "%s expects %d arguments, but got %d\n" name v1 v2
  | AlreadyDefinedError s ->
    Printf.printf "“%s” is already defined\n" s
  | ReplacingBoundWithConstant (name, omega) ->
    Printf.printf "Cannot replace bound variable “%s” with a constant “%s”\n"
      name (showTerm omega)
  | ReplacingWithBound (a, b) ->
    Printf.printf "Cannot replace “%s” with “%s”, because “%s” is bound" a b b
  | UnificationError (u, v) ->
    Printf.printf "“%s” cannot be unified with “%s”\n" (showTerm u) (showTerm v)
  | ExpectedVariable u ->
    Printf.printf "“%s” expected to be a variable" (showTerm u)
  | MatchError (u, v) ->
    Printf.printf "“%s” does not match “%s”\n" (showTerm u) (showTerm v)
  | AdmittedError -> print_endline "Admitted."
  | NotDefinedError s -> Printf.printf "“%s” is not defined\n" s
  | Sys_error s -> print_endline s
  | ex -> Printf.printf "Uncaught exception: %s\n" (Printexc.to_string ex)