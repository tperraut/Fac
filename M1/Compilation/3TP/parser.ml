
type token = 
  | WHILE
  | VAR
  | THEN
  | SEMI
  | RPAREN
  | PRINT
  | PLUS
  | OR
  | NOT
  | NEWLINE
  | NEQ
  | MULT
  | MINUS
  | LT
  | LPAREN
  | LE
  | IF
  | IDENT of (
# 25 "parser.mly"
       (Ast.ident)
# 24 "parser.ml"
)
  | GT
  | GE
  | EXIT
  | EQ
  | EOF
  | END
  | ELSE
  | DIV
  | CONST_INT of (
# 12 "parser.mly"
       (int)
# 37 "parser.ml"
)
  | CONST_BOOL of (
# 14 "parser.mly"
       (bool)
# 42 "parser.ml"
)
  | BEGIN
  | ASSIGN
  | AND

# 1 "parser.mly"
  

  open Astcommon
  open Ast

  let current_pos () =
    Parsing.symbol_start_pos (),
    Parsing.symbol_end_pos ()


# 59 "parser.ml"

let menhir_begin_marker =
  0

and (xv_unop, xv_prog, xv_list_instr_, xv_instr, xv_expr, xv_const, xv_block, xv_binop) =
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (xs : 'tv_list_instr_) (_startpos_xs_ : Lexing.position) (_endpos_xs_ : Lexing.position) (_startofs_xs_ : int) (_endofs_xs_ : int) (x : 'tv_instr) (_startpos_x_ : Lexing.position) (_endpos_x_ : Lexing.position) (_startofs_x_ : int) (_endofs_x_ : int) ->
    (
# 188 "/usr/share/menhir/standard.mly"
    ( x :: xs )
# 69 "parser.ml"
     : 'tv_list_instr_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 186 "/usr/share/menhir/standard.mly"
    ( [] )
# 75 "parser.ml"
     : 'tv_list_instr_) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 86 "parser.mly"
        ( Not    )
# 81 "parser.ml"
     : 'tv_unop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 85 "parser.mly"
        ( Uminus )
# 87 "parser.ml"
     : 'tv_unop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (instrs : 'tv_list_instr_) (_startpos_instrs_ : Lexing.position) (_endpos_instrs_ : Lexing.position) (_startofs_instrs_ : int) (_endofs_instrs_ : int) ->
    (
# 41 "parser.mly"
                          ( instrs )
# 93 "parser.ml"
     : (
# 36 "parser.mly"
      (Ast.prog)
# 97 "parser.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (b : 'tv_block) (_startpos_b_ : Lexing.position) (_endpos_b_ : Lexing.position) (_startofs_b_ : int) (_endofs_b_ : int) ->
    (
# 51 "parser.mly"
                                      ( Iblock b              )
# 103 "parser.ml"
     : 'tv_instr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (b : 'tv_block) (_startpos_b_ : Lexing.position) (_endpos_b_ : Lexing.position) (_startofs_b_ : int) (_endofs_b_ : int) (e : 'tv_expr) (_startpos_e_ : Lexing.position) (_endpos_e_ : Lexing.position) (_startofs_e_ : int) (_endofs_e_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 50 "parser.mly"
                                      ( Iwhile (e, Iblock(b)) )
# 109 "parser.ml"
     : 'tv_instr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 49 "parser.mly"
                                      ( Iexit                 )
# 115 "parser.ml"
     : 'tv_instr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 48 "parser.mly"
                                      ( Inewline              )
# 121 "parser.ml"
     : 'tv_instr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (e : 'tv_expr) (_startpos_e_ : Lexing.position) (_endpos_e_ : Lexing.position) (_startofs_e_ : int) (_endofs_e_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 47 "parser.mly"
                                      ( Iprint e              )
# 127 "parser.ml"
     : 'tv_instr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (e : 'tv_expr) (_startpos_e_ : Lexing.position) (_endpos_e_ : Lexing.position) (_startofs_e_ : int) (_endofs_e_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (id : (
# 25 "parser.mly"
       (Ast.ident)
# 132 "parser.ml"
  )) (_startpos_id_ : Lexing.position) (_endpos_id_ : Lexing.position) (_startofs_id_ : int) (_endofs_id_ : int) ->
    (
# 46 "parser.mly"
                                      ( Iassign (id, e)       )
# 137 "parser.ml"
     : 'tv_instr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (id : (
# 25 "parser.mly"
       (Ast.ident)
# 142 "parser.ml"
  )) (_startpos_id_ : Lexing.position) (_endpos_id_ : Lexing.position) (_startofs_id_ : int) (_endofs_id_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 45 "parser.mly"
                                      ( Idecl_var id          )
# 147 "parser.ml"
     : 'tv_instr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (e2 : 'tv_expr) (_startpos_e2_ : Lexing.position) (_endpos_e2_ : Lexing.position) (_startofs_e2_ : int) (_endofs_e2_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (e1 : 'tv_expr) (_startpos_e1_ : Lexing.position) (_endpos_e1_ : Lexing.position) (_startofs_e1_ : int) (_endofs_e1_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (c : 'tv_expr) (_startpos_c_ : Lexing.position) (_endpos_c_ : Lexing.position) (_startofs_c_ : int) (_endofs_c_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 64 "parser.mly"
                                           ( Eif (c, e1, e2)     )
# 153 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (e2 : 'tv_expr) (_startpos_e2_ : Lexing.position) (_endpos_e2_ : Lexing.position) (_startofs_e2_ : int) (_endofs_e2_ : int) (op : 'tv_binop) (_startpos_op_ : Lexing.position) (_endpos_op_ : Lexing.position) (_startofs_op_ : int) (_endofs_op_ : int) (e1 : 'tv_expr) (_startpos_e1_ : Lexing.position) (_endpos_e1_ : Lexing.position) (_startofs_e1_ : int) (_endofs_e1_ : int) ->
    (
# 63 "parser.mly"
                                           ( Ebinop (op, e1, e2) )
# 159 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (e : 'tv_expr) (_startpos_e_ : Lexing.position) (_endpos_e_ : Lexing.position) (_startofs_e_ : int) (_endofs_e_ : int) (op : 'tv_unop) (_startpos_op_ : Lexing.position) (_endpos_op_ : Lexing.position) (_startofs_op_ : int) (_endofs_op_ : int) ->
    (
# 62 "parser.mly"
                                           ( Eunop (op, e)       )
# 165 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (s : 'tv_expr) (_startpos_s_ : Lexing.position) (_endpos_s_ : Lexing.position) (_startofs_s_ : int) (_endofs_s_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 61 "parser.mly"
                                           ( s                   )
# 171 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (id : (
# 25 "parser.mly"
       (Ast.ident)
# 176 "parser.ml"
  )) (_startpos_id_ : Lexing.position) (_endpos_id_ : Lexing.position) (_startofs_id_ : int) (_endofs_id_ : int) ->
    (
# 60 "parser.mly"
                                           ( Eident id           )
# 181 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (c : 'tv_const) (_startpos_c_ : Lexing.position) (_endpos_c_ : Lexing.position) (_startofs_c_ : int) (_endofs_c_ : int) ->
    (
# 59 "parser.mly"
                                           ( c                   )
# 187 "parser.ml"
     : 'tv_expr) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (b : (
# 14 "parser.mly"
       (bool)
# 192 "parser.ml"
  )) (_startpos_b_ : Lexing.position) (_endpos_b_ : Lexing.position) (_startofs_b_ : int) (_endofs_b_ : int) ->
    (
# 68 "parser.mly"
               ( Econst (Cbool b) )
# 197 "parser.ml"
     : 'tv_const) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (i : (
# 12 "parser.mly"
       (int)
# 202 "parser.ml"
  )) (_startpos_i_ : Lexing.position) (_endpos_i_ : Lexing.position) (_startofs_i_ : int) (_endofs_i_ : int) ->
    (
# 67 "parser.mly"
               ( Econst (Cint i)  )
# 207 "parser.ml"
     : 'tv_const) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (instrs : 'tv_list_instr_) (_startpos_instrs_ : Lexing.position) (_endpos_instrs_ : Lexing.position) (_startofs_instrs_ : int) (_endofs_instrs_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 55 "parser.mly"
                                      ( instrs )
# 213 "parser.ml"
     : 'tv_block) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 82 "parser.mly"
        ( Ge    )
# 219 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 81 "parser.mly"
        ( Gt    )
# 225 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 80 "parser.mly"
        ( Le    )
# 231 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 79 "parser.mly"
        ( Lt    )
# 237 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 78 "parser.mly"
        ( Neq   )
# 243 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 77 "parser.mly"
        ( Eq    )
# 249 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 76 "parser.mly"
        ( Or    )
# 255 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 75 "parser.mly"
        ( And   )
# 261 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 74 "parser.mly"
        ( Div   )
# 267 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 73 "parser.mly"
        ( Mult  )
# 273 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 72 "parser.mly"
        ( Minus )
# 279 "parser.ml"
     : 'tv_binop) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 71 "parser.mly"
        ( Plus  )
# 285 "parser.ml"
     : 'tv_binop) in
  (raise Not_found : 'tv_unop * (
# 36 "parser.mly"
      (Ast.prog)
# 290 "parser.ml"
  ) * 'tv_list_instr_ * 'tv_instr * 'tv_expr * 'tv_const * 'tv_block * 'tv_binop)

and menhir_end_marker =
  0

# 220 "/usr/share/menhir/standard.mly"
  


# 300 "parser.ml"
