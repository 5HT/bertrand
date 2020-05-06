%{
  open Datatypes
%}

%token LPAR RPAR LSQR RSQR EOF
%token <string> IDENT
%token <int> INT

%start <Datatypes.sexp list> file

%%

cosexp:
  | sexp { [$1] }
  | sexp cosexp { $1 :: $2 }

sexp:
  | IDENT { Atom $1 }
  | INT { Int $1 }
  | LPAR cosexp RPAR { List $2 }
  | LSQR cosexp RSQR { Supp $2 }

file:
  | sexp file { $1 :: $2 }
  | EOF { [] }