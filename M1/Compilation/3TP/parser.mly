%{

  open Astcommon
  open Ast

  let current_pos () =
    Parsing.symbol_start_pos (),
    Parsing.symbol_end_pos ()

%}

%token <int> CONST_INT
%token PLUS MINUS MULT DIV
%token <bool> CONST_BOOL
%token AND OR NOT
%token EQ NEQ
%token GE GT LE LT
%token IF THEN ELSE
%token LPAREN RPAREN
%token SEMI
%token PRINT NEWLINE EXIT 
%token EOF
%token VAR BEGIN END WHILE
%token ASSIGN
%token <Ast.ident> IDENT

%nonassoc ELSE
%left OR
%left AND
%left NOT
%left EQ NEQ GE GT LE LT
%left PLUS MINUS
%left MULT DIV

%start prog
%type <Ast.prog> prog

%%

prog:
| instrs=list(instr); EOF { instrs }
;

instr:
| VAR; id=IDENT; SEMI                 { Idecl_var id          }
| id=IDENT; ASSIGN; e=expr; SEMI      { Iassign (id, e)       }    
| PRINT; e=expr; SEMI                 { Iprint e              }
| NEWLINE; SEMI                       { Inewline              }
| EXIT; SEMI                          { Iexit                 }
| WHILE; e=expr; b=block;             { Iwhile (e, b)         }
| b=block                             { Iblock b              }
;

block:
| BEGIN; instrs = list(instr); END;   { instrs }    
;
  
expr:
| c=const                                  { c                   }
| id=IDENT                                 { Eident id           }
| LPAREN; s=expr; RPAREN                   { s                   }
| op=unop; e=expr                          { Eunop (op, e)       }
| e1=expr; op=binop; e2=expr               { Ebinop (op, e1, e2) }
| IF; c=expr; THEN; e1=expr; ELSE; e2=expr { Eif (c, e1, e2)     }

const:
| i=CONST_INT  { Econst (Cint i)  }
| b=CONST_BOOL { Econst (Cbool b) }

%inline binop:
| PLUS  { Plus  }
| MINUS { Minus }
| MULT  { Mult  }
| DIV   { Div   }
| AND   { And   }
| OR    { Or    }
| EQ    { Eq    }
| NEQ   { Neq   }
| LT    { Lt    }
| LE    { Le    }
| GT    { Gt    }
| GE    { Ge    }
    
%inline unop:
| MINUS { Uminus }
| NOT   { Not    }
