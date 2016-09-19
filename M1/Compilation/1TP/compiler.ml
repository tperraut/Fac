open Ast
open Printf

(* Pour les questions bonus, voir fichier test failexprX.ml *)

let operator (op : Ast.binop) : string =
  match op with
    | Minus -> "sub"
    | Plus -> "add"
    | Div -> "div"
    | Mult -> "mul"

let rec compile_expr1 (e : Ast.expr) : unit =
  match e with
    | Eint(x) -> printf " li $a0, %d\n" x
    | Ebinop(op, bob, john) ->
        compile_expr1 bob;
        printf " sub $sp, $sp, 4\n sw $a0, 0($sp)\n";
        compile_expr1 john;
        printf " lw $a1, 0($sp)\n add $sp, $sp, 4\n %s $a0, $a1, $a0\n"
          (operator op)

let rec compile_expr2 (e : Ast.expr) (i : int) : unit =
  match e with
    | Eint(x) -> printf " li $a%d, %d\n" i x
    | Ebinop(op, bob, john) ->
        compile_expr2 bob i;
        compile_expr2 john (i + 1);
        printf " %s $a%d, $a%d, $a%d\n" (operator op) i i (i + 1)

let is_commute (op : Ast.binop) : bool =
  match op with
    | Minus -> false
    | _ -> true

(*
 * Nous considèrerons que les entiers utilisés sont codés sur 32 bits
 * sinon il faudra faire un petit ajustement
 *)

let rec compile_expr3 (e : Ast.expr) (i : int) : unit =
  match e with
    | Eint(x) -> printf " li $a%d, %d\n" i x
    | Ebinop(op, bob, john) ->
        match bob, john with
          | Eint(x), _ when (is_commute op) ->
              compile_expr3 john i;
              printf " %s $a%d, $a%d, %d\n" (operator op) i i x
          | Eint(_), Eint(x) ->
              compile_expr3 bob i;
              printf " %s $a%d, $a%d, %d\n" (operator op) i i x
          | _ ->
              compile_expr3 bob i;
              compile_expr3 john (i + 1);
              printf " %s $a%d, $a%d, $a%d\n" (operator op) i i (i + 1)

let rec require (e : Ast.expr) : int =
  match e with
    | Eint(x) -> 1
    | Ebinop(op, bob, john) ->
        match bob, john with
          | Eint(x), _ when (is_commute op) -> require john
          | Eint(_), Eint(x) -> require bob
          | _ -> require bob + require john

let compile_expr4 (e : Ast.expr) (req : int) : unit =
   match e with
     | Eint(x) -> 


let compile_toplevel_expr (e: Ast.expr) : unit =
  Printf.printf "registre required : %d\n" (require e);
  Printf.printf ".text\nmain:\n";
  compile_expr3 e 0;
  Printf.printf "#SYSTEM CALL\n";
  Printf.printf " li $v0, 1\n syscall\n li $v0, 10\n syscall\n"
