{
  open Parser
  open Lexing
}

let int    = ['0'-'9']
let bytes1 = [^ '\t' ' ' '\r' '\n' '(' ')' '[' ']' '0'-'9']
let bytes2 = ['\192'-'\223']['\128'-'\191']
let bytes3 = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4 = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']
let utf8   = bytes1|bytes2|bytes3|bytes4

let ws      = ['\t' ' ' '\r' '\n']
let nl      = ['\r' '\n']
let comment = ";" [^ '\n' '\r']* (nl|eof)

rule main = parse
| nl+ | ws+  { main lexbuf }
| comment    { main lexbuf }
| "("        { LPAR }
| ")"        { RPAR }
| "["        { LSQR }
| "]"        { RSQR }
| utf8+ as s { IDENT s }
| int+ as s  { INT (int_of_string s) }
| eof        { EOF }