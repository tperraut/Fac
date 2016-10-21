open Astcommon
open Ast
open Printf

(* Un type pour les environnements associant des variables [Astv.var] à des
   chaînes de caractères.
   Vous disposez en particulier des fonctions :

   Env.find : string -> var_env  -> Astv.var
   ... qui renvoie la variable associée à une chaîne de caractères

   Env.add  : string -> Astv.var -> var_env  -> var_env
   ... qui renvoie un nouvel environnement, étendu d'une association
   
   ainsi que de la constante Env.empty qui désigne un environnement vide.
*)
module Env = Map.Make(String)
type var_env = Astv.var Env.t

module Vset = Set.Make(struct type t = Astv.var let compare = compare end)
type var_set = Vset.t
  
(* Création d'une nouvelle variable à partir d'un identifiant.
   Remarque : faire apparaître l'identifiant dans la définition n'est pas
   nécessaire. Nous le proposons ici pour faciliter le débogage de votre
   compilateur. *)
let new_svar : ident -> Astv.var =
  let c = ref 0 in
  fun (id: ident) -> incr c; Astv.Static_var (!c, id)

let rec resolve_expr (env: var_env) : Ast.expr -> Astv.expr = function
  | Econst c ->
    Astv.Econst c

  (* Dans le cas d'un identifiant, on va chercher dans l'environnement la
     variables correspondante. *)
  | Eident id ->
    Astv.Evar (Env.find id env)
      
  | Eunop (op, e) ->
    Astv.Eunop (op, resolve_expr env e)
      
  | Ebinop (binop, e1, e2) ->
    Astv.Ebinop (binop, resolve_expr env e1, resolve_expr env e2)
      
  | Eif (e1, e2, e3) ->
    Astv.Eif (resolve_expr env e1, resolve_expr env e2, resolve_expr env e3)

  (* Dans le cas de la déclaration d'un tableau ou de l'accès à une case,
     on se content de traverser la structure de l'expression. *)
  | Enewarr e ->
    Astv.Enewarr (resolve_expr env e)

  | Egetarr (a, i) ->
    Astv.Egetarr (resolve_expr env a, resolve_expr env i)
      
let rec resolve_instr (env: var_env) : Ast.instr -> Astv.instr option * var_set * var_env =
  function
    (* La déclaration d'une variable ne produit pas d'instruction Astv,
       en revanche on renvoie le singleton formé par la nouvelle variable,
       et on l'ajoute à l'environnement. *)
    | Idecl_var id    ->
      let var = new_svar id in
      None, Vset.singleton var, Env.add id var env

    (* Dans le cas d'une affectation à une variable ou à une case de tableau,
       on produit une instruction Astv, mais aucune nouvelle variable, ni
       aucune modification de l'environnement. *)
    | Iassign (id, e) ->
      let svar = Env.find id env
      and e    = resolve_expr env e
      in
      Some (Astv.Iassign (svar, e)), Vset.empty, env
    | Idecl_ass (id, e) -> 
      let var = new_svar id
      and e    = resolve_expr env e
      in
      Some (Astv.Iassign (var, e)), Vset.singleton var, Env.add id var env

    | Isetarr (a, i, e) ->
      let a = resolve_expr env a
      and i = resolve_expr env i
      and e = resolve_expr env e
      in
      Some (Astv.Isetarr (a, i, e)), Vset.empty, env

    (* Dans le cas d'un bloc, on produit un bloc Astv. On renvoie l'ensemble
       des nouvelles variables donné par [resolve_block] (car des variables
       ont pu être déclarées dans le bloc, qui devront être allouées), mais
       on ne modifie pas l'environnement (car les variables déclarées dans
       le bloc ne sont plus visible à la sortie. *)
    | Iblock b ->
      let is, vset = resolve_block env b in
      Some (Astv.Iblock is), vset, env
	
    | Iwhile (c, b) ->
        let is, vset = resolve_block env b
        and e = resolve_expr env c
        in
        Some (Astv.Iwhile (e, is)), vset, env

    | Iprint e -> Some (Astv.Iprint (resolve_expr env e)), Vset.empty, env

    | Inewline -> Some Astv.Inewline, Vset.empty, env

    | Iexit    -> Some Astv.Iexit, Vset.empty, env

and resolve_block (env: var_env) : Ast.instr list -> Astv.block * var_set = function
  (* Un bloc de zéro instructions ne déclare pas de nouvelle variables. *)
  | [] -> [], Vset.empty
  | i::is ->
    (* Sinon, on commence par traduire la première instruction... *)
    let i, vs1, env = resolve_instr env i in
    (* ... puis le reste du bloc récursivement, en tenant compte de
       l'environnement [env] mis à jour. *)
    let is, vs2     = resolve_block env is in
    (* On combine les traductions de la première instruction et de la suite. *)
    let is = match i with
      | None -> is
      | Some i -> i :: is
    in
    (* À la fin, on fait l'union des ensembles [vs1] et [vs2] des variables 
       déclarées dans la première instruction et dans le reste du bloc. *)
    is, Vset.union vs1 vs2
      
let resolve_prog (p: Ast.prog) : Astv.prog =
  let is, vset = resolve_block Env.empty p in
  { Astv.instrs = is; Astv.svars = Vset.elements vset }
