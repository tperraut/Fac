
(* The type of tokens. *)

type token = 
  | STAR
  | SLASH
  | RPAREN
  | PLUS
  | MINUS
  | LPAREN
  | EOF
  | CONST_INT of (int)

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel_expr: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
