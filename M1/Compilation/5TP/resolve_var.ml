open Astcommon
open Ast
open Printf

module Env = Map.Make(String)
type var_env = Astv.var Env.t
    
(* Les environnements de type [fun_env] associent aux identifiants des
   noms désambigués de fonctions [Astv.fname], similaires à [Astv.var]
   pour les variables. *)
type fun_env = Astv.fname Env.t


module Vset = Set.Make(struct type t = Astv.var let compare = compare end)
type var_set = Vset.t

(* Un module pour les ensembles de déclarations de fonctions. *)
module Funset = Set.Make(struct type t = Astv.fun_descr let compare = compare end)
type fun_set = Funset.t
    
let new_svar =
  let c = ref 0 in
  fun id -> incr c; Astv.Static_var (!c, id)

(* Création d'un nouveau nom de fonction à partir d'un identifiant.
   Remarque : faire apparaître l'identifiant dans la définition n'est pas
   nécessaire. Nous le proposons ici pour faciliter le débogage de votre
   compilateur. *)
let new_fun =
  let c = ref 0 in
  fun id -> incr c; Astv.Function (!c, id)


(* La fonction [resolve_expr] prend en argument supplémentaire un environnement
   de fonctions. On a procédé à la mise à jour dans les cas corrigés. *)
let rec resolve_expr env fenv = function
  | Econst c ->
    Astv.Econst c
      
  | Eident id ->
    Astv.Evar (Env.find id env)
      
  | Eunop (op, e) ->
    Astv.Eunop (op, resolve_expr env fenv e)
      
  | Ebinop (binop, e1, e2) ->
    Astv.Ebinop (binop, resolve_expr env fenv e1, resolve_expr env fenv e2)
      
  | Eif (e1, e2, e3) ->
    Astv.Eif (resolve_expr env fenv e1, resolve_expr env fenv e2, resolve_expr env fenv e3)

  | Enewarr e ->
    Astv.Enewarr (resolve_expr env fenv e)

  | Egetarr (a, i) ->
    Astv.Egetarr (resolve_expr env fenv a, resolve_expr env fenv i)

  | Ecall c ->
    (* On propose ici de faire appel à une fonction spécifique pour résoudre
       les appels. Cette fonction servira également dans le cas [Icall]. *)
    Astv.Ecall (resolve_call env fenv c)

(* Fonction pour la résolution des identifiants au niveau d'un appel de
   fonction. *)
and resolve_call env fenv (f, args) =
  failwith "Not implemented"

    
(* La fonction de résolution des identifiants d'une instruction prend également
   en argument supplémentaire un environnement de fonctions.
   Elle renvoie en outre deux éléments supplémentaires :
   1/ Un ensemble de fonctions déclarées (type [fun_set]) similaire à
      l'ensemble de variables déjà présent.
   2/ Un environnement de fonctions (type [fun_env]) similaire à
      l'environnement de variables déjà présent.
   Ces arguments et résultats supplémentaires sont déjà mis à jour pour les
   cas corrigés.
*)
let rec resolve_instr env fenv =
  function
    | Idecl_var id    ->
      let var = new_svar id in
      None, Vset.singleton var, Env.add id var env, Funset.empty, fenv
    (*TODO*)
    | Idecl_fun (id, params, b) ->
        let fu = new_fun id
        and env2 = 
        and

    | Iassign (id, e) ->
      let svar = Env.find id env
      and e    = resolve_expr env fenv e
      in
      Some (Astv.Iassign (svar, e)), Vset.empty, env, Funset.empty, fenv

    | Isetarr (a, i, e) ->
      let a = resolve_expr env fenv a
      and i = resolve_expr env fenv i
      and e = resolve_expr env fenv e
      in
      Some (Astv.Isetarr (a, i, e)), Vset.empty, env, Funset.empty, fenv

    | Iblock b ->
      let is, vset, fset = resolve_block env fenv b in
      Some (Astv.Iblock is), vset, env, fset, fenv
	
    | Iwhile (c, is) ->
      let c  = resolve_expr env fenv c
      and is, vset, fset = resolve_block env fenv is
      in
      Some (Astv.Iwhile(c, is)), vset, env, fset, fenv
	
    | Iprint e ->
      Some (Astv.Iprint (resolve_expr env fenv e)), Vset.empty, env, Funset.empty, fenv

    | Inewline ->
      Some Astv.Inewline, Vset.empty, env, Funset.empty, fenv

    | Icall c ->
      Some (Astv.Icall (resolve_call env fenv c)), Vset.empty, env, Funset.empty, fenv
	(*TODO*)
    | Ireturn e ->
      failwith "Not implemented"
      
    | Iexit    ->
      Some Astv.Iexit, Vset.empty, env, Funset.empty, fenv

	
and resolve_block env fenv = function
  | [] -> [], Vset.empty, Funset.empty
  | i :: is ->
    let i, vs1, env, fs1, fenv = resolve_instr env fenv i  in
    let is, vs2, fs2           = resolve_block env fenv is in
    let is = match i with
      | None -> is
      | Some i -> i :: is
    in
    is, Vset.union vs1 vs2, Funset.union fs1 fs2
      
(* Deux itérateurs : un pour toplevel, et un pour les blocs.
   On passe en variables locales sur la pile les variables à l'intérieur
   des blocs. *)
      
let resolve_prog p =
  let is, vset, fset = resolve_block Env.empty Env.empty p in
  { Astv.instrs = is;
    Astv.svars = Vset.elements vset;
    Astv.funs = Funset.elements fset; }
