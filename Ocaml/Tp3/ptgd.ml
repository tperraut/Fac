(* Play The Game Dude ! *)
(* Struct *)
type valeur = Roi | Reine | Valet | Num of int;;
type couleur = Coeur | Pique | Trefle | Carreau;;
type carte = valeur * couleur;;
type paquet = carte list;;
(* End Struct *)
(* Function *)
let compare (v1,_) (v2,_) =
  if v1 = v2 then 0
  else match v1,v2 with
    | Roi, _ -> 1
    | Reine, Roi -> -1
    | Reine, _ -> 1
    | Valet, Roi -> -1
    | Valet, Reine -> -1
    | Valet, _ -> 1
    | Num(x), Num(y) -> (x - y) / (abs (x - y))
    | _ -> -1
;;
let str_of_clr c =
  match c with
    |Coeur -> "Coeur"
    |Pique -> "Pique"
    |Trefle -> "Trefle"
    |Carreau -> "Carreau"
;;
let string_of_carte (v, c) =
  match v with
    | Num(x) -> (string_of_int (x)) ^ " de " ^ (str_of_clr c)
    | Roi -> "Roi" ^ " de " ^ (str_of_clr c)
    | Reine -> "Reine" ^ " de " ^ (str_of_clr c)
    | Valet -> "Valet" ^ " de " ^ (str_of_clr c)
;;
let vv = [Roi; Reine; Valet; Num(10); Num(9); Num(8); Num(7);
          Num(6); Num(5); Num(4); Num(3); Num(2); Num(1)];;
let vvlen = List.length vv;;
let rec cc l_c c =
  if List.length l_c = vvlen then l_c
  else cc (c::l_c) c
;;
let p =
  (List.combine vv (cc [] Coeur))
  @ (List.combine vv (cc [] Pique))
  @ (List.combine vv (cc [] Trefle))
  @ (List.combine vv (cc [] Carreau));;
let rec echo_p p =
  match p with
    |[] -> Format.printf ""
    |x::s -> Format.printf "%s\n" (string_of_carte x); echo_p s
;;
let melange p1
;;
echo_p p;;
(* End Function *)
