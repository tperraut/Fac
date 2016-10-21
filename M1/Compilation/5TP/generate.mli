(** Ensemble des fonctions permettant de sauvegarder et de lire
    dans des registres particuliers
*)
val push : int -> unit
val peek : int -> unit
val pop : int -> unit

val new_label : unit -> string

(** Ensemble des fonctions permettant de créer un label unique
    correspondant à une variable ou une fonction.
*)
val get_label : Astv.var -> string
val get_fun_label : Astv.fname -> string

(** Fonctions permettant d'afficher le code assembleur correspondant
    aux éléments de l'ast [Astv]  *)
val generate_expr : Astv.expr -> unit
val generate_call : Astv.call -> unit
val generate_instr : Astv.instr -> unit
val generate_block : Astv.block -> unit
val generate_fun : Astv.fun_descr -> unit

(** Fonctions appelées afin d'initialiser le code avec certaines
    instructions nécessaires à toute bonne exécution *)
val init : unit -> unit
val system_vars : unit -> unit
val end_exec : unit -> unit
val built_ins : unit -> unit
val constants : unit -> unit

(** Fonction principale du module affichant le code assembleur 
    correspondant au fichier source en se basant sur l'ast [Astv]
    ayant été généré. *)
val generate_prog : Astv.prog -> unit
