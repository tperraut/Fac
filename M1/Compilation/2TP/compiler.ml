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
      let op = match op with
	| Plus  -> "add"
	| Mult  -> "mul"
	| Minus -> "sub"
	| Div   -> "div"
	| _     -> assert false
      in
      printf "  %s $a0, $a0, %d\n" op i

      (* Opération arithmétique ordinaire *)
    | Ebinop (op, e1, e2) ->
      (* 1. on calcule le résultat du premier opérande *)
      compile_expr e1;
      (* 2. on le sauvegarde sur la pile *)
      push 0;
      (* 3. on calcule le résultat du deuxième opérande *)
      compile_expr e2;
      (* 4. on récupère sur la pile le premier résultat *)
      pop 1;
      (* 5. on effectue l'opération *)
      let op = match op with
	| Plus -> "add"
	| Mult -> "mul"
	| Minus -> "sub"
	| Div  -> "div"
	| _    -> failwith "Not implemented"
      in
      printf "  %s $a0, $a1, $a0\n" op

    (* À vous de jouer ! *)
    | _ -> failwith "Not implemented"

(* Compilation d'une expression à la racine : on affiche d'abord le préambule,
   puis le code correspondant à l'expression, et enfin le code d'affichage et
   d'arrêt du programme. *)
let compile_toplevel_expr (e: Ast.expr) : unit =
  printf ".text\nmain:\n";
  compile_expr e;
  printf "  li $v0, 1\n  syscall\n  li $v0, 10\n  syscall\n"
