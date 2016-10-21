open Astcommon

type var = Static_var of int * Ast.ident
	   | Param    of int * Ast.ident
	   | Local_var of int * Ast.ident
type fname = Function   of int * Ast.ident
    
type expr =
  | Econst  of const
  | Evar    of var
  | Eunop   of unop  * expr
  | Ebinop  of binop * expr * expr
  | Eif     of expr  * expr * expr
  | Enewarr of expr
  | Egetarr of expr  * expr
  | Ecall   of call
and call = fname * expr list

type block = instr list
and  instr =
  | Iassign   of var  * expr
  | Isetarr   of expr * expr  * expr
  | Iblock    of block
  | Iwhile    of expr * block
  | Iprint    of expr
  | Inewline
  | Ireturn   of expr
  | Icall     of call
  | Iexit

type fun_descr = { name: fname; body: block; nb_locals: int }
      
type prog = { instrs: instr list;
	      svars: var list;
	      funs: fun_descr list; }
