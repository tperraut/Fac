(** Module représentant des dictionnaire ayant pour clés
    des chaînes de caractères
*)
module Env : Map.S with type key = String.t

(** Dictionnaire associant des variables [Astv.var] à des 
    chaînes de caractères. *)
type var_env = Astv.var Env.t

(** Les environnements de type [fun_env] associent aux identifiants des
    noms désambigués de fonctions [Astv.fname], similaires à [Astv.var]
    pour les variables. *)
type fun_env = Astv.fname Env.t

module Vset : Set.S with type elt = Astv.var

type var_set = Vset.t
    
(** Un module pour les ensembles de déclarations de fonctions. *)
module Funset : Set.S with type elt = Astv.fun_descr

type fun_set = Funset.t

(** Fonctions permettant d'associer à chaque identifiants (de variables ou
    de fonctions) des un entier unique qui servira pour
    [Generate.get_label] ou [Generate.get_fun_label] *)
val new_svar : Ast.ident -> Astv.var
val new_fun : Ast.ident -> Astv.fname

(** Fonctions permettant de transformer des éléments de l'ast créé par
    le parser (donc du module [Ast]) en éléments du nouvel ast (module [Astv])
    
    Le type de ses fonctions n'est pas figé et peut (doit) bien évidemment
    être augmenté en fonctions des besoins (on remarquera, par exemple, 
    l'ajout du type [fun_env] pour gérer le dictionnaire de fonctions)
*)

val resolve_expr : var_env -> fun_env -> Ast.expr -> Astv.expr
val resolve_call : var_env -> fun_env -> Ast.call -> Astv.call
val resolve_instr : var_env -> fun_env -> Ast.instr ->
  Astv.instr option * var_set * var_env * fun_set * fun_env
val resolve_block : var_env -> fun_env -> Ast.block ->
  Astv.block * var_set * fun_set

(** Fonction principale du module, seule fonction appelée à l'extérieur.
    Son type ne doit pas être changé au risque d'entraîner un conflit
    avec d'autres modules l'utilisant.
 *)
val resolve_prog : Ast.prog -> Astv.prog
