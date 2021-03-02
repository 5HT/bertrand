open Sexp
open Errors
open Lexing
open Prelude
open Checker
open Datatypes

type cmdline =
  | Check of string
  | Html  of string
  | Help

let banner = "PRINCIPIA theorem prover\n"
let help =
"   invoke = principia | principia list
          | principia html filename
     list = [] | command list
  command = check filename | help"

let rec chain : string list -> cmdline list = function
  | [] -> []
  | "check" :: filename :: rest -> Check filename :: chain rest
  | "help"  :: rest -> Help :: chain rest
  | x :: xs ->
    Printf.printf "Unknown/incorrect command “%s”\n" x;
    chain xs

let args : string list -> cmdline list = function
  | "html" :: filename :: [] -> [Html filename]
  | xs                       -> print_endline banner; chain xs

let defaults : cmdline list -> cmdline list = function
  | [] -> [Help]
  | xs -> xs

let cmd : cmdline -> unit = function
  | Check filename -> Elaborator.dofile filename
  | Html  filename -> Html.html         filename
  | Help -> print_endline help

let () =
  Array.to_list Sys.argv
  |> List.tl  |> args
  |> defaults |> List.iter cmd