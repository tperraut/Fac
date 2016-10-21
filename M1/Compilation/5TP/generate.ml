open Astcommon
open Astv
open Printf
  
let push = printf "  sub $sp, $sp, 4\n  sw $a%d, 0($sp)\n"

let peek = printf "  lw $a%d, 0($sp)\n"

let pop = printf "  lw $a%d, 0($sp)\n  add $sp, $sp, 4\n"

let new_label =
  let c = ref 0 in
  fun () -> incr c; sprintf "__label__%05i" !c

let get_label = function
  | Astv.Static_var (n, id) -> sprintf "__var__%05i__%s" n id
  | _ -> assert false

(* Association d'une étiquette à un nom de fonction. *)
let get_fun_label = function
  | Astv.Function (n, id) -> sprintf "__fun__%05i__%s" n id
    
let rec generate_expr e = 
  match e with
      
    | Econst (Cint i)  -> printf "  li $a0, %d\n" i
    | Econst (Cbool b) -> printf "  li $a0, %d\n" (if b then 1 else 0)

    | Evar var ->
      (* Il y a maintenant plusieurs cas de variables à traiter. *)
      begin match var with
	| Static_var _ -> printf "  la $a0, %s\n  lw $a0, 0($a0)\n" (get_label var)
	| Param (n, _) -> failwith "Not implemented"
	| Local_var (n, _)  -> failwith "Not implemented"
      end

    | Eunop (Uminus, e) ->
      generate_expr e;
      printf "  neg $a0, $a0\n"
    | Eunop (Not, e) ->
      generate_expr e;
      printf "  li $a1, 1\n  sub $a0, $a1, $a0\n"
      
    | Ebinop ((Plus | Mult) as op, Econst (Cint i), e)
    | Ebinop ((Plus | Mult | Minus | Div) as op, e, Econst (Cint i))
	when -32768 <= i && i < 32768 ->
      generate_expr e;
      let op = match op with
	| Plus -> "add"
	| Mult -> "mul"
	| Minus -> "sub"
	| Div  -> "div"
	| _    -> assert false
      in
      printf "  %s $a0, $a0, %d\n" op i
	
    | Ebinop (op, e1, e2) ->
      generate_expr e1;
      push 0;
      generate_expr e2;
      pop 1;
      let op = match op with
	| Plus -> "add"
	| Mult -> "mul"
	| Minus -> "sub"
	| Div  -> "div"
	(* Les autres opérateurs binaires correspondent directement
	   à des instructions MIPS. *)
	| Eq   -> "seq"
	| Neq  -> "sne"
	| Lt   -> "slt"
	| Le   -> "sle"
	| Gt   -> "sgt"
	| Ge   -> "sge"
	| And  -> "and"
	| Or   -> "or"
      in
      printf "  %s $a0, $a1, $a0\n" op

    | Eif (c, e_then, e_else) ->
      let else_label = new_label()
      and end_label  = new_label()
      in
      generate_expr c;
      printf "  beqz $a0, %s\n" else_label;
      generate_expr e_then;
      printf "  b %s\n" end_label;
      printf "%s:\n" else_label;
      generate_expr e_else;
      printf "%s:\n" end_label

    | Enewarr e ->
      (* Le calcul de [e] donne la taille du tableau, qu'on sauvegarde. *)
      generate_expr e;
      push 0;
      (* On en déduit le nombre d'octets nécessaire avant d'appeler [malloc]. *)
      printf "  add $a0, $a0, 1\n  mul $a0, $a0, 4\n";
      printf "  jal malloc\n";
      (* Enfin, on récupère la taille du tableau pour l'enregistrer dans
	 l'entête du bloc. *)
      pop 1;
      printf "  sw $a1, 0($a0)\n"
      

    | Egetarr (e, i) ->
      (* Calcul et sauvegarde de l'adresse du tableau. *)
      generate_expr e;
      push 0;
      (* Calcul de l'indice regardé. *)
      generate_expr i;
      (* De l'indice on déduit le décalage à demander. *)
      printf "  add $a0, $a0, 1\n mul $a0, $a0, 4\n";
      (* Récupération de l'adresse du tableau, puis accès. *)
      pop 1;
      printf "  add $a0, $a1, $a0\n";
      printf "  lw  $a0, 0($a0)\n"

    | Ecall c ->
      generate_call c

and generate_call (fname, exprs) =
  (* On a besoin ici du code correspondant aux actions de l'appelant. *)
  failwith "Not implemented"

(* Génération de code pour les blocs. *)
let rec generate_instr = function

  | Iassign (var, e) ->
    generate_expr e;
    begin match var with
      | Static_var _ ->
	printf "  la $a1, %s\n  sw $a0, 0($a1)\n" (get_label var)
      | Local_var (n, id) -> failwith "Not implemented"
      | Param _ -> failwith "Not implemented"
    end
      
  | Isetarr (a, i, e) ->
    (* Calcul et sauvegarde de l'adresse du tableau. *)
    generate_expr a;
    push 0;
    (* Calcul et sauvegarde de l'indice. *)
    generate_expr i;
    push 0;
    (* Calcul de la valeur à stocker. *)
    generate_expr e;
    (* Récupération de l'indice et calcul du décalage en octets. *)
    pop 1;
    printf "  add $a1, $a1, 1\n  mul $a1, $a1, 4\n";
    (* Récupération de l'adresse du tableau et accès. *)
    pop 2;
    printf "  add $a1, $a2, $a1\n";
    printf "  sw  $a0, 0($a1)\n"
	
  | Iblock b      -> generate_block b
    
  | Iwhile (c, b) ->
    let cond_label = new_label()
    and end_label  = new_label()
    in
    printf "%s:\n" cond_label;
    generate_expr c;
    printf "  beqz $a0, %s\n" end_label;
    generate_block b;
    printf "  b %s\n" cond_label;
    printf "%s:\n" end_label
    
  | Iprint e ->
    generate_expr e;
    printf "  li $v0, 1\n  syscall\n"
      
  | Inewline ->
    printf "  li $v0, 11\n  li $a0, 10\n  syscall\n"
      
  | Iexit ->
    printf "  li $v0, 10\n  syscall\n"

  | Icall c ->
    generate_call c

  | Ireturn e ->
    failwith "Not implemented"
    
and generate_block b = List.iter generate_instr b

let generate_fun fdescr =
  (* On a besoin ici du code correspondant aux actions de l'appelée. *)
  failwith "Not implemented"
  
let init () = printf "
  li  $a0, 1024       # Appel système sbrk pour réserver 1024 octets.
  li  $v0, 9
  syscall

  la  $a0, nxt_loc    # L'appel système a placé dans $v0 l'adresse de début
  sw  $v0, 0($a0)     # de la zone réservée, à sauvegarder dans nxt_loc.

  add $v0, $v0, 1024  # Calcul de max_loc, 1024 octets plus loin.
  la  $a0, max_loc   
  sw  $v0, 0($a0)
                      # Initialisation terminée.

"

let system_vars () = printf "
nxt_loc:
  .word 0
max_loc:
  .word 0
"

let end_exec () = printf "
end_exec:                       # Fin de l'exécution
  li $v0, 10
  syscall
"
    
let built_ins () = printf "
malloc:
  la   $v0, nxt_loc             # Sauvegarde de l'adresse de début de bloc
  lw   $v1, 0($v0)

  add  $a1, $v1, $a0            # Calcul de l'adresse de fin...
  la   $a2, max_loc
  lw   $a2, 0($a2)
  bgt  $a1, $a2, out_of_memory  # ... et arrêt en cas de dépassement

  sw   $a1, 0($v0)              # Sinon confirmation de l'allocation
  move $a0, $v1
  jr   $ra                      # et retour au point d'appel

out_of_memory:                  # Affichage d'un message d'erreur
  la $a0, __const_out_of_memory
  li $v0, 4
  syscall
  b end_exec
"

let constants () = printf "
__const_out_of_memory:
  .asciiz \"out of memory\"
"

let generate_prog p =
  (* Le code. *)  
  printf "  .text\nmain:\n";
  (* 1. Initialisation. *)
  init ();
  (* 2. Le programme lui-même. *)
  List.iter generate_instr p.instrs;
  end_exec ();
  (* 2'. Les fonctions définies par l'utilisateur. *)
  List.iter generate_fun p.funs;
  (* 3. Les fonctions primitives. *)
  built_ins ();

  (* Les données. *)
  printf "  .data\n";
  (* 1. Les variables utilisées par les primitives. *)
  system_vars ();
  constants ();
  (* 2. Les variables de l'utilisateur. *)
  List.iter (fun var -> printf "%s:\n  .word 0\n" (get_label var)) p.svars
