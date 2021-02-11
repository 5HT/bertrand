%{
  open Datatypes
%}

%token LPAR RPAR LSQR RSQR EOF
%token <string> IDENT

%start <Datatypes.sexp list> file

%%

cosexp:
  | { [] }
  | sexp cosexp { $1 :: $2 }

sexp:
  | IDENT { Atom $1 }
  | LPAR cosexp RPAR { List $2 }
  | LSQR cosexp RSQR { Supp $2 }

file:
  | sexp file { $1 :: $2 }
  | EOF { [] }