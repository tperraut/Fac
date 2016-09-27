type unop  =
  | Uminus
  | Not

type binop =
  | Plus | Minus | Mult | Div
  | And  | Or
  | Eq   | Neq   | Lt   | Le  | Gt | Ge

type const =
  | Cint  of int
  | Cbool of bool

type expr =
  | Econst of const
  | Eunop  of unop  * expr
  | Ebinop of binop * expr * expr
  | Eif    of expr  * expr * expr
