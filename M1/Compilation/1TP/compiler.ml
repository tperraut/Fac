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
    | Minus | Div -> false
    | _ -> true

(*
 * Nous considèrerons que les entiers utilisés sont codés sur 32 bits
 * sinon il faudra faire un petit ajustement ou utiliser un jeu
 * d'instructions 64 bits
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
          | Eint(_), Eint(_) -> 1
          | Eint(_), _ when (is_commute op) -> require john
          | _ ->
              let r1 = require bob in
              let r2 = require john in
                if r1 > r2 then r1 + 1
                else r2 + 1

(* Peut être testé avec arith6.ml pour le bon fonctionnement *)
let rec compile_expr4 (e : Ast.expr) (i : int) : unit =
  match e with
    | Eint(x) -> printf " li $a%d, %d\n" i x
    | Ebinop(op, bob, john) ->
        match bob, john with
          | Eint(x), _ when (is_commute op) ->
              compile_expr4 john i;
              printf " %s $a%d, $a%d, %d\n" (operator op) i i x
          | Eint(_), Eint(x) ->
              compile_expr4 bob i;
              printf " %s $a%d, $a%d, %d\n" (operator op) i i x
          | _ when (require bob) > (require john) ->
                      compile_expr4 bob i;
                      compile_expr4 john (i + 1);
                      printf " %s $a%d, $a%d, $a%d\n" (operator op) i i (i + 1)
                      | _ ->
                          compile_expr4 john i;
                          compile_expr4 bob (i + 1);
                          printf " %s $a%d, $a%d, $a%d\n" (operator op) i (i + 1) i

(*let rec compile_expr5 (e : Ast.expr) (i : int) : unit =
 match e with
 | Eint(x) -> printf " li $a%d, %d\n" i x
 | Ebinop(op, bob, john) ->
 match bob, john with
 | Eint(x), _ when (is_commute op) ->
 compile_expr5 john i;
 printf " %s $a%d, $a%d, %d\n" (operator op) i i x
 | Eint(_), Eint(x) ->
 compile_expr5 bob i;
 printf " %s $a%d, $a%d, %d\n" (operator op) i i x
 | _ when (require bob) > (require john) ->
 compile_expr5 bob i;
 compile_expr5 john (i + 1);
 printf " %s $a%d, $a%d, $a%d\n" (operator op) i i (i + 1)
 | _ ->
 compile_expr4 john i;
 compile_expr4 bob (i + 1);
 printf " %s $a%d, $a%d, $a%d\n" (operator op) i (i + 1) i
 *)


(*let rec pretty_print (e : expr) : unit =
  match e with
    | Eint(x) -> printf "%d" x
    | Ebinop(op, e1, e2) ->
        match e1, e2 with
          | Eint _, Eint _ ->
              pretty_print e1;
              printf "%s" (op_toString op);
              pretty_print e2
          | Eint _, Ebinop(ope, _, _) ->
              pretty_print e1;
              printf "%s" (op_toString op);
              if par op ope then
                begin
                  printf "(";
                  pretty_print e2;
                  printf ")"
                end
              else
                pretty_print e2
          | Ebinop(ope, _, _), Eint _ ->
              if par op ope then
                begin
                  printf "(";
                  pretty_print e1;
                  printf ")";
                end
              else
                pretty_print e1;
              printf "%s" (op_toString op);
              pretty_print e2
          | Ebinop(op1, _, _), Ebinop(op2, _, _) ->
              if par op op1 then
                begin
                  printf "(";
                  pretty_print e1;
                  printf ")";
                end
              else
                pretty_print e1;
              printf "%s" (op_toString op);
              if par op op2 then
                begin
                  printf "(";
                  pretty_print e2;
                  printf ")"
                end
              else
                pretty_print e2
 *)
let rpar (o1 : binop) (o2 : binop) : bool =
  match o1, o2 with
    | Mult, Plus
    | Mult, Minus
    | Minus, Plus
    | Minus, Minus
    | Div, _ -> true
    |_ -> false

let lpar (o1 : binop) (o2 : binop) : bool =
  match o1, o2 with
    | Plus, Mult
    | Plus, Div
    | Minus, Mult
    | Minus, Div -> true
    | _ -> false

let op_toString (op : binop) : string =
  match op with
    | Mult -> " * "
    | Div -> " / "
    | Plus -> " + "
    | Minus -> " - "

let pretty_print (e : expr) : unit =
  match e with
    | Eint(x) -> printf "%d" x
    | Ebinop(op, e1, e2) ->
        let rec pprint (e : expr) (o : binop) (sag : bool) : unit =
          (*sag definie si e est dans un sous arbre gauche ou droit*)
          match e, sag with
            | Eint(x), _ -> printf "%d" x
            | Ebinop(op, e1, e2), true when lpar op o ->
                printf "(";
                pprint e1 op true;
                printf "%s" (op_toString op);
                pprint e2 op false;
                printf ")"
            | Ebinop(op, e1, e2), false when rpar o op ->
                printf "(";
                pprint e1 op true;
                printf "%s" (op_toString op);
                pprint e2 op false;
                printf ")"
            | Ebinop(op, e1, e2), _->
                pprint e1 op true;
                printf "%s" (op_toString op);
                pprint e2 op false;
        in
          pprint e1 op true;
          printf "%s" (op_toString op);
          pprint e2 op false

let rec tostring e =
  match e with
    | Eint i -> Printf.printf "%d" i
    | Ebinop (ex, o1, o2) ->
        begin
          let s = match ex with | Plus -> "+" | Minus -> "-" | Mult -> "*" | Div -> "/" in 
          let f1 = 
            match o1 with
              | Eint _ -> false
              | Ebinop (ex1,o11,o12) ->
                  match ex, ex1 with
                    | Div, Plus | Mult, Plus | Div, Minus | Mult, Minus -> true
                    | _,_ -> false
                               and f2 =
                                 match o2 with
                                   | Eint _ -> false
                                   | Ebinop (ex1,o11,o12) ->
                                       match ex, ex1 with
                                         | Mult, Plus | Mult, Minus | Div, _ | Minus, Plus | Minus, Minus -> true
                                         | _,_ -> false
          in 
            (if f1 then Printf.printf "( ");tostring o1;(if f1 then Printf.printf " )"); Printf.printf " %s " s; (if f2 then Printf.printf "( ");tostring o2;if f2 then Printf.printf " )" 
        end

let rec echo_expr (e : Ast.expr) : unit =
  match e with
    | Eint x -> printf "%d" x
    | Ebinop(op, e1, e2) ->
        printf "%s(" (op_toString op);
        echo_expr e1;
        printf ", ";
        echo_expr e2;
        printf ")"

let compile_toplevel_expr (e: Ast.expr) : unit =
  let e = Ebinop(Minus, Ebinop(Plus, Eint(1), Eint(2)), Eint(3)) in
    echo_expr e;
    Printf.printf "\nMoi : ";
    pretty_print e;
    Printf.printf "\n";
    Printf.printf "Toi : ";
    tostring e;
    Printf.printf "\n#base registre required : %d\n" (require e);
    Printf.printf ".text\nmain:\n";
    compile_expr4 e 0;
    Printf.printf "#SYSTEM CALL\n";
    Printf.printf " li $v0, 1\n syscall\n li $v0, 10\n syscall\n"
