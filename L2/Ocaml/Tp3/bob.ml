(*
 * Ceci est un echauffement
 * type f = char list -> char -> bool
*)
let rec f x y =
  match x with
    | [] -> true
    | (0, _ ) :: _ -> false
    | (a, _) :: _ when a=y ->  false
    | _ :: t -> f t y
;;

let rec sum p l =
  match l with
    | [] -> p
    | x :: s -> sum (p + x) s
;;

(*A little test*)
let a = 1::2::3::4::5::[];;
Format.printf "%d\n" (sum 0 a);;
(**)
