open Astcommon

type var = Static_var of int * Ast.ident
    
type expr =
  | Econst of const
  | Evar   of var
  | Eunop  of unop  * expr
  | Ebinop of binop * expr * expr
  | Eif    of expr  * expr * expr

type block = instr list
and  instr =
  | Iassign  of var  * expr
  | Iblock   of block
  | Iwhile   of expr * block
  | Iprint   of expr
  | Inewline
  | Iexit
      
type prog = { instrs: instr list; svars: var list }
