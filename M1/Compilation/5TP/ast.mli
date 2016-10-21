open Astcommon

type ident = string

type expr =
  | Econst  of const
  | Eident  of ident
  | Eunop   of unop  * expr
  | Ebinop  of binop * expr * expr
  | Eif     of expr  * expr * expr
  | Enewarr of expr
  | Egetarr of expr  * expr
  | Ecall   of call
and call = ident * expr list

type block = instr list
and  instr =
  | Idecl_var of ident
  | Idecl_fun of ident * ident list * block
  | Idecl_rfun of ident * ident list * block
  | Iassign   of ident * expr
  | Isetarr   of expr  * expr  * expr
  | Iblock    of block
  | Iwhile    of expr  * block
  | Iprint    of expr
  | Inewline
  | Icall     of call
  | Ireturn   of expr
  | Iexit
      
type prog = instr list
