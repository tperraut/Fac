type position = Lexing.position * Lexing.position

type binop = Plus | Minus | Mult | Div

type expr =
  | Eint   of int
  | Ebinop of binop * expr * expr
