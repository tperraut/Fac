open Ast
open Printf

(* Les fonctions [push] et [pop] prennent en argument un numéro de registre [i]
 et affichent le code correspondant à 
 [push] : placer sur la pile la valeur contenue dans le registre [$ai]
 [pop]  : transférer dans [$ai] la valeur présente au sommet de la pile
 *)
let push: int -> unit =
  printf "  sub $sp, $sp, 4\n  sw $a%d, 0($sp)\n"

let pop: int -> unit =
  printf "  lw $a%d, 0($sp)\n  add $sp, $sp, 4\n"


(* Création d'une nouvelle étiquette pour les branchements. *)
let new_label : unit -> string =
  let c = ref 0 in
    fun () -> incr c; sprintf "__label__%05i" !c

let ope (op : Ast.binop) :  string =
  match op with
    | Plus  -> "add"
    | Mult  -> "mul"
    | Minus -> "sub"
    | Div   -> "div"
    | And -> "and"
    | Or -> "or"
    | Ge | Lt | Gt | Le -> "slt"
    | Neq -> "ne"
    | Eq -> "eq"

let if_ope (op : Ast.binop) :  string =
  match op with
    | Plus  -> "add"
    | Mult  -> "mul"
    | Minus -> "sub"
    | Div   -> "div"
    | And -> "and"
    | Or -> "or"
    | Ge | Lt | Neq -> "eq"
    | Gt | Le | Eq -> "ne"
(*int_of_bool*)
let iob : bool -> int = function
  | true -> 1
  | _ -> 0
(* Compilation des expressions.
 Le code produit place le résultat dans le registre [$a0]. *)
let rec compile_expr (e : Ast.expr) : unit =
  match e with
    (* Constante : on charge directement la valeur dans le registre. *)
    | Econst (Cint i) -> printf "  li $a0, %d\n" i

    (* Opération arithmétique dont l'un des opérandes peut être utilisé
     directement (sans passer par un registre).
     Il faut que cet opérande soit une constante sur 16 bits signée.
     Elle peut être le deuxième opérande de n'importe quelle opération
     arithmétique, ou le premier opérande d'une opération commutative
     (addition ou multiplication). *)
    | Ebinop ((Plus | Mult) as op, Econst (Cint i), e)
    | Ebinop ((Plus | Mult | Minus | Div) as op, e, Econst (Cint i))
        when -32768 <= i && i < 32768 ->
        (* On calcule d'abord l'opérande qui n'est pas immédiat. *)
        compile_expr e;
        (* Puis on effectue l'opération. *)
        printf "  %s $a0, $a0, %d\n" (ope op) i

    (* Opération arithmétique ordinaire *)
    | Ebinop ((Plus | Mult | Minus | Div) as op, e1, e2) ->
        (* 1. on calcule le résultat du premier opérande *)
        compile_expr e1;
        (* 2. on le sauvegarde sur la pile *)
        push 0;
        (* 3. on calcule le résultat du deuxième opérande *)
        compile_expr e2;
        (* 4. on récupère sur la pile le premier résultat *)
        pop 1;
        (* 5. on effectue l'opération *)
        printf "  %s $a0, $a1, $a0\n" (ope op)
    | Eunop (Uminus, Econst (Cint i)) when -32768 < i && i <= 32768
      -> printf "  li $a0, -%d\n" i
    | Ebinop (Lt as op, e1, e2) ->
        (* 1. on calcule le résultat du premier opérande *)
        compile_expr e1;
        (* 2. on le sauvegarde sur la pile *)
        push 0;
        (* 3. on calcule le résultat du deuxième opérande *)
        compile_expr e2;
        (* 4. on récupère sur la pile le premier résultat *)
        pop 1;
        (* 5. on effectue l'opération *)
        printf "  %s $a0, $a1, $a0\n" (ope op)
    | Ebinop (Le as op, e1, e2) ->
        (* 1. on calcule le résultat du premier opérande *)
        compile_expr e1;
        (* 2. on le sauvegarde sur la pile *)
        push 0;
        (* 3. on calcule le résultat du deuxième opérande *)
        compile_expr e2;
        (* 4. on récupère sur la pile le premier résultat *)
        pop 1;
        (* 5. on effectue l'opération, toute les op sont remplacée par slt
        * car c'est le seul alias disponible dans la doc mips *)
        printf "  %s $a0, $a0, $a1\n  xori $a0, $a0, 1\n" (ope op)
    (* Opérations boléenne *)
    | Econst (Cbool b) -> printf "  li $a0, %d\n" (iob b)
    | Eunop (Not, e1) ->
        compile_expr e1;
        printf "  not $a0, $a0\n"
    | Ebinop (And, e1, e2) ->
        let label = new_label () in
          (* 1. on calcule le résultat du premier opérande *)
          compile_expr e1;
          (* 2. on jump si e1 est évalué à faux *)
          printf "  beq $a0, 0, %s\n" label;
          (* 3. on calcule le résultat du deuxième opérande *)
          compile_expr e2;
          (* 4. on met le label *)
          printf "%s:\n" label
    | Ebinop (Or, e1, e2) ->
        let label = new_label () in
          (* 1. on calcule le résultat du premier opérande *)
          compile_expr e1;
          (* 2. on jump si e1 est évalué à vrai *)
          printf "  bne $a0, 0, %s\n" label;
          (* 3. on calcule le résultat du deuxième opérande *)
          compile_expr e2;
          (* 4. on met le label *)
          printf "%s:\n" label
    | Eif (e1, e2, e3) ->
        let l_else = new_label () in
        let l_end = new_label () in
          (* IF *)
          if_compile_expr e1 l_else;
          (* THEN *)
          compile_expr e2;
          printf "  j %s\n%s:\n" l_end l_else;
          (* ELSE *)
          compile_expr e3;
          printf "%s:\n" l_end
            (* TODO au cas ou le parser n'est pas parfait *)
    | _ -> failwith "Not implemented"

and if_compile_expr (e : Ast.expr) (label : string): unit =
  match e with
    | Econst (Cbool b) ->
        printf "  li $a0, %d\n  beq $a0, 0, %s\n" (iob b) label
    | Eunop (Not, Econst (Cbool b)) ->
        printf "  li $a0, %d\n  bne $a0, 0, %s\n" (iob (not b)) label
    | Ebinop (Lt | Ge as op, e1, e2) ->
        (* 1. on calcule le résultat du premier opérande *)
        compile_expr e1;
        (* 2. on le sauvegarde sur la pile *)
        push 0;
        (* 3. on calcule le résultat du deuxième opérande *)
        compile_expr e2;
        (* 4. on récupère sur la pile le premier résultat *)
        pop 1;
        (* 5. saut sur else dans les bon moment*)
        printf "  slt $a0, $a1, $a0\n  b%s $a0, 0, %s\n" (if_ope op) label
    | Ebinop (Le | Gt as op, e1, e2) ->
        (* 1. on calcule le résultat du premier opérande *)
        compile_expr e1;
        (* 2. on le sauvegarde sur la pile *)
        push 0;
        (* 3. on calcule le résultat du deuxième opérande *)
        compile_expr e2;
        (* 4. on récupère sur la pile le premier résultat *)
        pop 1;
        (* 5. saut sur else dans les bon moment*)
        printf "  slt $a0, $a0, $a1\n  b%s $a0, 0, %s\n" (if_ope op) label
    | Ebinop (Eq | Neq as op, e1, e2) ->
        (* 1. on calcule le résultat du premier opérande *)
        compile_expr e1;
        (* 2. on le sauvegarde sur la pile *)
        push 0;
        (* 3. on calcule le résultat du deuxième opérande *)
        compile_expr e2;
        (* 4. on récupère sur la pile le premier résultat *)
        pop 1;
        (* 5. saut sur else dans les bon moment*)
        printf "  b%s $a0, $a1, %s\n" (if_ope op) label
    | Ebinop (And, e1, e2) ->
          (* 1. on calcule le résultat du premier opérande
          * On imbrique ici e1 dans une sorte de if pour ne pas faire
          * l'évaluation de e2 si e1 faux et aller directement au ELSE
          * du IF parent *)
          if_compile_expr e1 label;
          (* 2. on calcule le résultat du deuxième opérande *)
          if_compile_expr e2 label;
    | Ebinop (Or, e1, e2) ->
          let l_then = new_label () in
          (* 1. on calcule le résultat du premier opérande *)
          compile_expr e1;
          (* 2. si e1 est évalué à vrai, on jump directement sans
          * calculer e2 *)
          printf "  bne $a0, 0, %s\n" l_then;
          (* 3. on calcule le résultat du deuxième opérande *)
          if_compile_expr e2 label;
          printf "%s:\n" l_then
    | Eif (e1, e2, e3) ->
        let l_else = new_label () in
        let l_end = new_label () in
          (* IF *)
          if_compile_expr e1 l_else;
          (* THEN *)
          compile_expr e2;
          printf "  j %s\n%s:\n" l_end l_else;
          (* ELSE *)
          compile_expr e3;
          printf "%s:\n" l_end;
          printf "  beq $a0, 0, %s\n" label
    (* TODO au cas ou le parser n'est pas parfait *)
    | _ -> failwith "Not implemented"

(* Compilation d'une expression à la racine : on affiche d'abord le préambule,
 puis le code correspondant à l'expression, et enfin le code d'affichage et
 d'arrêt du programme. *)
let compile_toplevel_expr (e: Ast.expr) : unit =
  printf ".text\nmain:\n";
  compile_expr e;
  printf "# SYSCALL #\n  li $v0, 1\n  syscall\n  li $v0, 10\n  syscall\n\n"
