open Ast

type value = Int of int | Bool of bool
  
let rec interpret_expr (e : Ast.expr) : value =
  match e with
    | Econst c ->
      begin match c with
	| Cint i  -> Int i
	| Cbool b -> Bool b
      end
    | Eunop (op, e) ->
      let v = interpret_expr e in
      begin match op, v with
	| Uminus, Int i  -> Int (-i)
	| Not,    Bool b -> Bool (not b)
	| _, _           -> failwith "Expression mal formée"
      end
    | Ebinop (op, e1, e2) ->
      let v1 = interpret_expr e1
      and v2 = interpret_expr e2
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
    | Eif(c, e1, e2) ->
      begin match interpret_expr c with
	| Bool b when b -> interpret_expr e1
	| Bool b        -> interpret_expr e2
	| _             -> failwith "Expression mal formée"
      end
