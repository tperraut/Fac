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
  | '\n' (* Actions en cas de retour à la ligne :
	    1. enregistrer le changement de ligne dans le tampon [lexbuf]
	       (utile pour localiser les erreurs)
	    2. relancer l'analyse en rappelant la fonction [token] sur [lexbuf]
	  *)
      { new_line lexbuf; token lexbuf }
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
      { failwith "Lexical error" }
and comment = parse
  | '\n' { new_line lexbuf; comment lexbuf }
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | _
      { comment lexbuf }
  | eof
      {failwith "Commentaire non-fermé"}
