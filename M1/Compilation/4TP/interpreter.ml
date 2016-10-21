open Astcommon
open Ast

exception Exit
exception Undefined
  
type value = Int of int | Bool of bool | Array of value array | Undefined

module Env = Map.Make(String)
type venv  = value ref Env.t
    
let rec interpret_expr (env : venv) : Ast.expr -> value = function

  | Econst c ->
    begin match c with
      | Cint i  -> Int i
      | Cbool b -> Bool b
    end
      
  | Eident id -> !(Env.find id env)
    
  | Eunop (op, e) ->
    let v = interpret_expr env e in
    begin match op, v with
      | Uminus, Int i  -> Int (-i)
      | Not,    Bool b -> Bool (not b)
      | _, _           -> failwith "Expression mal formée"
    end
      
  | Ebinop (op, e1, e2) ->
    let v1 = interpret_expr env e1
    and v2 = interpret_expr env e2
    in
    begin match (op, v1, v2) with
      | (Plus | Minus | Mult | Div) as op, Int i1, Int i2 ->
	let i = match op with
	  | Plus -> i1 + i2
	  | Mult -> i1 * i2
	  | Minus -> i1 - i2
	  | Div  -> i1 / i2
	  | _    -> assert false
	in Int i
      | (And | Or) as op, Bool b1, Bool b2 ->
	let b = match op with
	  | And -> b1 && b2
	  | Or  -> b1 || b2
	  | _   -> assert false
	in Bool b
      | (Eq | Neq | Lt | Le | Gt | Ge) as op, Int i1, Int i2 ->
	let b = match op with
	  | Eq  -> i1 =  i2
	  | Neq -> i1 <> i2
	  | Lt  -> i1 <  i2
	  | Le  -> i1 <= i2
	  | Gt  -> i1 >  i2
	  | Ge  -> i1 >= i2
	  | _   -> assert false
	in Bool b
      | _, _, _ -> failwith "Expression mal formée"
    end
      
  | Eif (c, e1, e2) ->
    begin match interpret_expr env c with
      | Bool b when b -> interpret_expr env e1
      | Bool b        -> interpret_expr env e2
      | _             -> failwith "Expression mal formée"
    end

  | Enewarr n ->
    begin match interpret_expr env n with
      | Int n -> Array (Array.make n Undefined)
      | _     -> failwith "Expression mal formée"
    end

  | Egetarr (arr, idx) ->
    begin match (interpret_expr env arr, interpret_expr env idx) with
      | Array a, Int i -> a.(i)
      | _              -> failwith "Expression mal formée"
    end

let print_value : value -> unit = function
  | Int i     -> print_int i
  | Bool b    -> if b then print_int 1 else print_int 0
  | Array a   -> print_int 0
  | Undefined -> print_int 0
      
let rec interpret_instr (env: venv) : instr -> venv = function
  | Idecl_var id    -> Env.add id (ref Undefined) env
  | Iassign (id, e) -> Env.find id env := interpret_expr env e; env
  | Idecl_ass (id, e) ->
      let env = Env.add id (ref Undefined) env
      in
        Env.find id env := interpret_expr env e; env
  | Isetarr (arr, idx, e) ->
    begin
      match (interpret_expr env arr, interpret_expr env idx) with
	| Array a, Int i -> a.(i) <- interpret_expr env e
	| _              -> failwith "Expression mal formée"
    end; env
  | Iblock b        -> interpret_block env b; env
  | Iwhile (c, b)   -> while match interpret_expr env c with
                             | Bool b -> b
			     | _      -> failwith "Expression mal formée"
		       do interpret_block env b done; env
  | Iprint e        -> print_value (interpret_expr env e); env
  | Inewline        -> print_newline (); env
  | Iexit           -> raise Exit

and interpret_block (env: venv) (b: block) : unit =
  ignore (List.fold_left interpret_instr env b)
    
let interpret_prog (p: prog) : unit =
  try  interpret_block Env.empty p
  with Exit -> ()
