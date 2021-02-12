open Sexp
open Errors
open Lexing
open Prelude
open Checker
open Datatypes

type cmdline =
  | Check of string
  | Help

let banner = "PRINCIPIA theorem prover\n"
let help =
"   invoke = principia | principia list
     list = [] | command list
  command = check filename | help"

let rec parseArgs : string list -> cmdline list = function
  | [] -> []
  | "check" :: filename :: rest -> Check filename :: parseArgs rest
  | "help"  :: rest -> Help :: parseArgs rest
  | x :: xs ->
    Printf.printf "Unknown command “%s”\n" x;
    parseArgs xs

let defaults : cmdline list -> cmdline list = function
  | [] -> [Help]
  | xs -> xs

let cmd : cmdline -> unit = function
  | Check filename -> Elaborator.dofile filename
  | Help -> print_endline help

let () =
  print_endline banner;
  Array.to_list Sys.argv
  |> List.tl  |> parseArgs
  |> defaults |> List.iter cmd