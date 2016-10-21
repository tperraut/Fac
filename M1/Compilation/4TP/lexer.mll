{

  open Lexing
  open Parser
  open Ast

  let lexical_error s =
    failwith ("Lexical error : " ^ s)
    
  let comment_cpt = ref 0      

  (* Fonction auxiliaire appelée lorsque l'on reconnaît une suite de lettres.
     Si cette suite de lettres correspond à un mot clé, alors la fonction renvoie
     le lexème correspondant. Sinon, elle échoue.
  *)
  let keyword =
    let h = Hashtbl.create 17 in
    List.iter (fun (s, k) -> Hashtbl.add h s k)
      [ "true",  CONST_BOOL(true);
	"false", CONST_BOOL(false);
	"not",   NOT;
	"if",    IF;
	"then",  THEN;
	"else",  ELSE;
	"print", PRINT;
	"newline", NEWLINE;
	"exit",  EXIT;
	"var", VAR;
        "while", WHILE;
        "for", FOR;
        "to", TO;
	"begin", BEGIN;
	"end", END;
      ]	;
    fun s ->
      try  Hashtbl.find h s
      with Not_found -> IDENT s
	
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = ['a'-'z'](digit|alpha|'_')*

rule token = parse
  | '\n'
      { new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r']+
      { token lexbuf }
  | "(*"
      { incr comment_cpt; comment lexbuf; token lexbuf }
  | digit+
      { CONST_INT (int_of_string (lexeme lexbuf)) }
  (* En cas d'une suite de lettre, traitement par la fonction auxiliaire pour
     les mots clés. *)
  | ident
      { keyword (lexeme lexbuf) }
  | "("
      { LPAREN }
  | ")"
      { RPAREN }
  | "["
      { LSPAREN }
  | "]"
      { RSPAREN }
  | "-"
      { MINUS }
  | "+"
      { PLUS }
  | "*"
      { MULT }
  | "/"
      { DIV }
  | "=="
      { EQ }
  | "!="
      { NEQ }
  | ">"
      { GT }
  | ">="
      { GE }
  | "<"
      { LT }
  | "<="
      { LE }
  | "&&"
      { AND }
  | "||"
      { OR }
  | ";"
      { SEMI }
  | ":="
      { ASSIGN }
(* Fin *)
  | _
      { lexical_error (lexeme lexbuf) }
  | eof
      { EOF }

and comment = parse
  | "(*"
      { incr comment_cpt; comment lexbuf }
  | "*)"
      { decr comment_cpt; if !comment_cpt > 0 then comment lexbuf }
  | _
      { comment lexbuf }
  | eof
      { lexical_error "unterminated comment" }
