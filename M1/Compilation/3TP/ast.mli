open Astcommon

type ident = string

type expr =
  | Econst of const
  | Eident of ident
  | Eunop  of unop  * expr
  | Ebinop of binop * expr * expr
  | Eif    of expr  * expr * expr

type block = instr list
and  instr =
  | Idecl_var of ident
  | Iassign   of ident * expr
  | Iblock    of block
  | Iwhile    of expr  * block
  | Iprint    of expr
  | Inewline
  | Iexit
      
type prog = instr list
