%{

  open Ast

  (* Vous pouvez insérer ici du code Caml pour définir des fonctions
     ou des variables qui seront utilisées dans les actions sémantiques. *)

  %}

(* Définition des lexèmes. *)
%token EOF
%token PLUS MINUS MULT DIV
%token LPAREN RPAREN
%token <int> CINT

(* Règles d'associativité et de priorité. *)
%left PLUS MINUS
%left MULT DIV
(* Symbole de départ et type de la valeur produite par l'action sémantique. *)
%start toplevel_expr
%type <Ast.expr> toplevel_expr

%%

(* Règles. *)

toplevel_expr:
    (* Expression à la racine : une expression [expr] dont on notera [e] la valeur
   sémantique, suivie du symbole [EOF].
   La valeur sémantique associée est la valeur [e] de l'expression.
   *)
| e=expr; EOF { e }
;

expr:
    | ci = CINT
    {Econst (Cint (ci))}
    | e1 = expr; PLUS; e2 = expr
    {Ebinop (Plus, e1, e2)}
    | e1 = expr; MINUS; e2 = expr
    {Ebinop (Minus, e1, e2)}
    | e1 = expr; DIV; e2 = expr
    {Ebinop (Div, e1, e2)}
    | e1 = expr; MULT; e2 = expr
    {Ebinop (Mult, e1, e2)}
    | LPAREN e = expr RPAREN
    {e}
| EOF { failwith "Unlikely" }
;
