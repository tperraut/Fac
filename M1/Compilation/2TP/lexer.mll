{

  open Lexing
  open Parser
  open Ast

  (* Vous pouvez insérer ici du code Caml pour définir des fonctions
     ou des variables qui seront utilisées dans les actions sémantiques. *)
}

let space = [' ' '\t' '\r']+
let digit = ['0'-'9']

rule token = parse
  | '\n'
  {new_line lexbuf; token lexbuf}
  | space {token lexbuf}
  | digit+ as i
  {CINT (int_of_string i)}
  (*{INT (int_of_string (lexeme lexbuf))}*)
  | "(*" {comment lexbuf; token lexbuf}
  | "(" {LPAREN}
  | ")" {RPAREN}
  | "+" {PLUS}
  | "-" {MINUS}
  | "*" {MULT}
  | "/" {DIV}
  | eof
  { EOF }
  | _
      { failwith "Lexical error" }
  and comment = parse
  | "*)"
  {()}
  | "(*"
  {comment lexbuf; comment lexbuf}
  |_
  { comment lexbuf }
  | eof
  {failwith "Commentaire non-fermé."}
