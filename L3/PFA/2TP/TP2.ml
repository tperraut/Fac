(*
  Info 311 - Programmation fonctionnelle avancée - TP3
  Nom : PERRAUT
  Prénom : Thomas
  Numéro étudiant : 21217952
  *)


(* A enlever pour la compilation.
   (ligne de compilation: ocamlc graphics.cma [options] <filename>
    ou ocamlopt graphics.cmxa [options] <filename>) *)
(*load "graphics.cma";;*)

open Graphics

let black = Graphics.black
let white = Graphics.white


type 'a t =
    | F of 'a
  | N of 'a t * 'a t * 'a t * 'a t
type image = int t

(* Exemple du TP. *)
let a0 = N (N (F white,F black,F black,F black),F black,F white,F black)
let t0 = [|
    [| white ; black ; white ; white |] ;
    [| black ; black ; white ; white |] ;
    [| black ; black ; black ; black |] ;
    [| black ; black ; black ; black |]
    |]

let rec get_pixel x y longueur arbre =
    let l2 = longueur/2 in
    match arbre with
        | F(couleur) -> couleur
        | N(so, se, no, ne) -> match (x, y) with
            |(x, y) when x<l2 &&  y<l2 -> get_pixel x y l2 so 
            |(x, y) when x>=l2 && y<l2 -> get_pixel x y l2 se
            |(x, y) when x<l2 && y>=l2 -> get_pixel x y l2 no
            |(x, y) when x>=l2 && y>=l2 -> get_pixel x y l2 ne
;;


let image_matrix_of_tree longueur arbre =
    Array.init longueur (fun i -> Array.init longueur (fun j -> get_pixel i j longueur arbre))
;;

exception BoolFalse of bool;;

let  monochrome_color image_matrix x y longueur couleur =
    try
        for i = x to x+longueur-1 do
            for j = y to y+longueur-1 do
                if couleur != image_matrix.(i).(j) then raise (BoolFalse false)
            done
            done

        ;	true
        with BoolFalse false -> false

;;

let image_tree_of_matrix image_matrix x y longueur =
    let rec image_tree_aux image_matrix x y l =
        let l2 = l/2 in
        if (monochrome_color image_matrix x y l image_matrix.(x).(y) ) then F(image_matrix.(x).(y))
        else N(image_tree_aux image_matrix (x) (y) l2, image_tree_aux image_matrix (x+ l2) (y) l2, image_tree_aux image_matrix (x) (y + l2) l2, image_tree_aux image_matrix (x + l2) (y + l2) l2)
        in
    image_tree_aux image_matrix x y longueur
;;

let aff_tab t taille =
    for i = 0 to (taille-1) do
        for j = 0 to (taille-1) do
            if t.(i).(j) = black then print_string ("noir ") else print_string("blanc ")
        done;
        print_string("\n")
        done;
;;

let compress image_matrix =
    image_tree_of_matrix image_matrix 0 0 (Array.length image_matrix)
;;


(*Test question 1*)
let c = get_pixel 2 1 4 a0;;
if (c = black) then print_string("Q1 ok\n") else print_string("Q1 pas ok\n");;

(*Test question 2*)
let tab = image_matrix_of_tree 4 a0 in
if (tab = t0) then print_string ("Q2 ok\n") else print_string("Q2 pas ok\n");;

(*Test question 3*)
let () = if (monochrome_color t0 2 2 2 black = true) then print_string("Q3 ok\n") else print_string("Q3 pas ok\n");;

(* Test question 4*)
let test = image_tree_of_matrix t0 0 0 4;;
let test2 = image_matrix_of_tree 4 test;;
let () = aff_tab test2 4;;
print_string("\n");;
let () = aff_tab t0 4;;
