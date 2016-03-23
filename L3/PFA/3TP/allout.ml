open Grapgics;;

let lancer_interface n =
    let s = string_of_int n in
    open_graph (" " ^ s ^ "x" ^ x)
;;

let fermer_interface () =
    close_graph ()
;;

let dessiner_grille g =
;;

let attendre_coup () =
    let event = wait_next_event [Button_down;Key_pressed] in
    if (
    (event.mx, event.my)

let nouvelle_grille n =
    let _ = Random.self_init () in
    Array.init n (fun _ -> Array.init n (fun _ -> Random.bool ()))
;;
