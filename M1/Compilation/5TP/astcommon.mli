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
