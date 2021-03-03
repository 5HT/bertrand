open Sexp
open Errors
open Parser
open Prelude
open Checker
open Datatypes
open Elaborator

(* HTML renderer from https://github.com/o1/nitro/blob/master/src/nitro.sml *)
type attr =
  | IntAttr   of string * int
  | StrAttr   of string * string
  | ListAttr  of string * string list
  | NoValAttr of string

type elem =
  | Liter    of string
  | Singular of { tag : string; attrs : attr list }
  | Tag      of { tag : string; attrs : attr list; childs : elem list }

let text s = Liter s

let singular name attrs =
  Singular { tag = name; attrs = attrs }
let tag name attrs childs =
  Tag { tag = name; attrs = attrs; childs = childs }

let div = tag "div"
let tr  = tag "tr"
let td  = tag "td"
let th  = tag "th"

(* Attributes *)
let noval v       = NoValAttr v
let id v          = StrAttr ("id", v)
let colspan v     = IntAttr ("colspan", v)
let style v       = StrAttr ("style", v)
let bgcolor v     = StrAttr ("bgcolor", v)
let charset v     = StrAttr ("charset", v)
let cellspacing v = IntAttr ("cellspacing", v)
let cellpadding v = IntAttr ("cellpadding", v)
let size v        = IntAttr ("size", v)
let align v       = StrAttr ("align", v)

let attrVal = function
  | IntAttr (name, v)  -> (name, string_of_int v)
  | StrAttr (name, v)  -> (name, v)
  | ListAttr (name, v) -> (name, String.concat " " v)
  | NoValAttr name     -> (name, "")

let rendAttr att =
  match attrVal att with
  | (name, "") -> name
  | (name, v)  -> name ^ "=\"" ^ v ^ "\""

let renderAttrs =
  List.map rendAttr >> String.concat " "

let rec render = function
  | Tag {tag; attrs; childs} ->
    let body  = String.concat " " (List.map render childs) in
    let attrs = renderAttrs attrs in
    "<" ^ tag ^ " " ^ attrs ^ ">" ^ body ^ "</" ^ tag ^ ">"
  | Singular {tag; attrs} ->
    "<" ^ tag ^ " " ^ renderAttrs attrs ^ " />"
  | Liter str -> str

let mathjax = "
<script>
  MathJax = {
    tex: {
      inlineMath: [
        ['$', '$']
      ],
      displayMath: [
        ['$$', '$$'],
      ],
    },
    svg: {
      fontCache: 'global'
    },
    loader: {load: ['input/tex', 'output/svg']}
  };
</script>
<script src=\"https://polyfill.io/v3/polyfill.min.js?features=es6\"></script>
<script id=\"MathJax-script\" async
        src=\"https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js\">
</script>
"

let descriptions : (string SMap.t) ref = ref SMap.empty

let nodata = "―"
let getDesc name = Option.value (SMap.find_opt name !descriptions) ~default:nodata

let termTex : term -> string =
  let rec render : term -> string = function
    | Lit s                   -> Printf.sprintf "\\textrm{%s}" s
    | FVar (s, _)             -> s
    | Var  (s, _)             -> s
    | Symtree (Lit "@" :: xs) -> "[" ^ space xs ^ "]"
    | Symtree xs              -> "(" ^ space xs ^ ")"
    | Hole                    -> "_"
  and space xs =
    String.concat " \\space " (List.map render xs) in

  function
  | Symtree xs -> space xs
  | tau        -> render tau

let quoteTex s = "$$" ^ s ^ "$$"
let tex tau = Liter (quoteTex (termTex tau))

let premises rule =
  if List.length rule.premises > 0 then begin
    tr [] [
      td [colspan 3; align "center"] [
        List.map termTex rule.premises
        |> String.concat " \\quad "
        |> quoteTex |> text
      ]
    ] :: []
  end else []

let decl rule =
  premises rule @ [
    tr [] [
      td [colspan 3; align "center"] [
        tex rule.conclusion
      ]
    ]
  ]

let declHeader kind name desc =
  tr [bgcolor "#eeeeee"] [
    td [] [text kind];
    td [] [text name];
    td [] [text desc]
  ]

let tags : command -> elem list = function
  | Variables xs     -> variables xs;  []
  | Constants xs     -> constants xs;  []
  | Infix (op, prec) -> infix op prec; []
  | Description xs   ->
    List.iter (fun (name, desc) ->
      descriptions := SMap.add name desc !descriptions) xs; []
  | Axiom xs ->
    List.map (fun (name, rule) ->
      declHeader "Axiom" name (getDesc name) :: decl rule) xs
    |> List.concat
  | Decl { name; hypothesises; rule; proof } ->
    declHeader "Theorem" name (getDesc name) :: decl rule
  | Macro (pattern, body, desc) ->
    declHeader "Definition" nodata
      (Option.value desc ~default:nodata) ::
    tr [] [
      td [colspan 3; align "center"] [
        termTex pattern ^ " ≔ " ^ termTex body
        |> quoteTex |> text
      ]
    ] :: []
  | _ -> []

let tableHeader =
  tr [] [
    th [align "left"; style "width: 10%;"] [text "Type"];
    th [align "left"; style "width: 10%;"] [text "Label"];
    th [align "left"] [text "Description"]
  ]

let html filename =
  let table = List.concat (run List.map tags [] filename) in
  tag "html" [] [
    tag "head" [] [
      singular "meta" [charset "UTF-8"];
      text mathjax;
      tag "title" [] [text "PRINCIPIA"]
    ];
    tag "body" [] [
      tag "table" [
        cellspacing 0; cellpadding 3; align "center";
        noval "border"; style "width: 70%;"
      ] (tableHeader :: table)
    ]
  ]
  |> render
  |> print_endline