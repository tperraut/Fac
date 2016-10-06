{
  open Lexing
  open Parser
  open Ast

  (* Vous pouvez insérer ici du code Caml pour définir des fonctions
     ou des variables qui seront utilisées dans les actions sémantiques. *)	 
  exception Error of string

  let newline lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <-
      { pos with Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
		 Lexing.pos_bol = pos.Lexing.pos_cnum }
	
  let parse_error lexbuf message =
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    let lexem = Lexing.lexeme lexbuf in
    let msg = Printf.sprintf "Line %d, character %d: \027[31m %s \027[0m\nUnbound lexem: %s" line cnum message lexem in
    raise (Error (msg))
}

let space = [' ' '\t' '\r']+
let digit = ['0'-'9']
	      
rule token = parse
  | '\n' (* Actions en cas de retour à la ligne :
	    1. enregistrer le changement de ligne dans le tampon [lexbuf]
	       (utile pour localiser les erreurs)
	    2. relancer l'analyse en rappelant la fonction [token] sur [lexbuf]
	  *)
      { newline lexbuf; token lexbuf }
  | space { token lexbuf }
  | "true" { CBOOL (true) }
  | "false" { CBOOL (false) }
  | digit+ as i
		{ CINT ( int_of_string i ) }
  | "(*" { comment lexbuf; token lexbuf }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { MULT }
  | "/" { DIV }
  | "&&" { AND }
  | "||" { OR }
  | "==" { EQ }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "!=" { NEQ }
  | "<" { LT }
  | "<=" { LE }
  | ">" { GT }
  | ">=" { GE }
  | "not" { NOT }
  | eof  (* Fin de fichier : émission du lexème [EOF] *)
      { EOF }
  | _
      { parse_error lexbuf "Lexical error" }
and comment = parse
  | '\n' { newline lexbuf; comment lexbuf }
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | _
      { comment lexbuf }
  | eof
      {parse_error lexbuf "Commentaire non-fermé"}
