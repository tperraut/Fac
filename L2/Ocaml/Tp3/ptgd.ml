(* 
** THOMAS PERRAUT
** 2014-2015
*)

(* Play The Game Dude ! *)
(* Struct *)
(* Q1 valeur, couleur, carte et paquet *)
type value = Roi | Reine | Valet | Num of int;;
type color = Coeur | Pique | Trefle | Carreau;;
type card = value * color;;
type packet = card list;;
(* End Struct *)
(* Function and some const *)
(* Q2 compare*)
let compare_card (v1,_) (v2,_) =
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
(* Q3 string_of_carte *)
let string_of_color c =
  match c with
    |Coeur -> "Coeur"
    |Pique -> "Pique"
    |Trefle -> "Trefle"
    |Carreau -> "Carreau"
;;
let string_of_card (v, c) =
  match v with
    | Num(x) -> (string_of_int (x)) ^ " de " ^ (string_of_color c)
    | Roi -> "Roi" ^ " de " ^ (string_of_color c)
    | Reine -> "Reine" ^ " de " ^ (string_of_color c)
    | Valet -> "Valet" ^ " de " ^ (string_of_color c)
;;
(* Q4 paquet *)
(* List of all card values *)
let vv = [Roi; Reine; Valet; Num(10); Num(9); Num(8); Num(7);
          Num(6); Num(5); Num(4); Num(3); Num(2); Num(1)];;
let vvlen = List.length vv;;
(* Create a list with vvlen element of the given color *)
let rec cc l_c c =
  if List.length l_c = vvlen then l_c
  else cc (c::l_c) c
;;
(* Create a 52 packet card *)
let p = (List.combine vv (cc [] Coeur))
  @ (List.combine vv (cc [] Pique))
  @ (List.combine vv (cc [] Trefle))
  @ (List.combine vv (cc [] Carreau));;
let plen = List.length p;;
(* TEST Print a packet
let rec echo_p pck =
  match pck with
    |[] -> Format.printf ""
    |x::s -> Format.printf "%s\n" (string_of_card x); echo_p s
;;
*)
(*
** Mix a packet
** Source : http://stackoverflow.com/questions/15095541/how-to-shuffle-list-in-on-in-ocamls
** My idea was the second one in the given link but this one looks very nice
*)
(* Q5 mélange *)
let mix pck =
  let nd = List.map (fun c -> (Random.bits (), c)) pck in
  let sond = List.sort compare nd in
  List.map snd sond
;;
(* Q6 partage*)
(*
** Split a packet in 2 equal packet.
** Return a pair of null packet if the two paquet cannot be equal
** (Little change of the prototype partage : paquet -> paquet -> paquet * paquet)
*)
let rec split_equal l1 l2 =
  let l1len = List.length l1 in
  let l2len = List.length l2 in
  if l1len = l2len then (List.rev l1, l2)
  else
    match l2 with
      |[] -> ([],[])
      |x::s -> split_equal (x::l1) s
;;
(* Q7 face_a_face *)
(* Give the new score after a face to face *)
let face_to_face (s1, s2) c1 c2 =
  let comp = compare_card c1 c2 in
  match comp with
   |(-1) -> (s1, s2 + 1)
   |1 -> (s1 + 1, s2)
   |_ -> (s1, s2)
;;
(* Q8 face_a_face_texte*)
let string_of_score (s1, s2) =
  "(" ^ string_of_int(s1) ^ ", " ^ string_of_int(s2) ^ ")"
;;
(* face_to_face with output *)
let face_to_face_text (s1, s2) c1 c2 =
  let comp = compare_card c1 c2 in
  match comp with
   | -1 -> Format.printf "Score de depart : %s\n  %s VS %s\nScore finale : %s\n"
              (string_of_score (s1, s2)) (string_of_card c1) (string_of_card c2)
              (string_of_score (s1, s2 + 1));
           (s1, s2 + 1)
   | 1 -> Format.printf "Score de depart : %s\n  %s VS %s\nScore finale : %s\n"
            (string_of_score (s1, s2)) (string_of_card c1) (string_of_card c2)
            (string_of_score (s1 + 1, s2));
        (s1 + 1, s2)
   | _ -> Format.printf "Score de depart : %s\n  %s VS %s\nScore finale : %s\n"
            (string_of_score (s1, s2)) (string_of_card c1) (string_of_card c2)
            (string_of_score (s1, s2));
        (s1, s2)
;;
(* Q9 bataille*)
(* Play the game *)
let rec playend (s1, s2) (p1, p2) =
  match p1, p2 with
  | [], _  -> (s1, s2)
  | _, []  -> (s1, s2)
  | c1::l1, c2::l2 -> playend (face_to_face (s1, s2) (c1) (c2)) (l1, l2)
;;
let war () =
  let pck = mix p in
  let pp = split_equal [] pck in
  playend (0, 0) pp
;;
(* Some test
echo_p p;;
echo_p (fst(split_equal [] (mix p)));;
Format.printf "-------------------\n";;
echo_p (snd(split_equal [] (mix p)));;
face_to_face_text (0, 0) (Roi, Pique) (Reine, Carreau);;
Format.printf "%s\n" (string_of_score (playend (0, 0) ([], p)));;
let score = war ();;
*)
(* Q10 stat*)
(* Let's make some stats ! *)
let diffone (a, b) =
  if a - b > 0 then 1
  else 0
;;
(* Add score to cumulate score and add a victory to the victorious player *)
let vic_cum ((sum1, v1), (sum2, v2)) (s1, s2)=
  match s1, s2 with
  | _, _ -> ((sum1 + s1, v1 + diffone (s1, s2)), (sum2 + s2, v2 + diffone (s2, s1)))
;;
(*
** Play n games and give number of victory and cumulate score for all players like
** ((Score_player1, Victory_player1)(Score_player2, Victory_player2))
*)
let rec war_n i n jj=
  match i with
    | _ when i = n -> jj
    | _ -> war_n (i + 1) n (vic_cum jj (war ()))
;;

let stat n =
  let result = war_n 0 n ((0, 0),(0, 0)) in
  match result with
    | ((s1, v1), (s2, v2)) ->
        Format.printf "Joueur 1 :\n  Victoire : %d\n  Score cumule : %d\n  Score moyen : %d\n  Taux de victoire : %d %s\n\n"
          v1 s1 (s1 / n) (v1 * 100 / n) "%";
        Format.printf "Joueur 2 :\n  Victoire : %d\n  Score cumule : %d\n  Score moyen : %d\n  Taux de victoire : %d %s\n\n"
          v2 s2 (s2 / n) (v2 * 100 / n) "%"; 0
;;
(* Do one million games in 1m40s with less than 5Mo of ram
let x = stat 1000000;;
*)
let main () =
  let ac =Array.length Sys.argv in
  match ac with
  | 1 -> Format.printf "Too few arguments\n"
  | _ when ac > 2 -> Format.printf "Too many arguments\n"
  | _ -> try if (stat (int_of_string (Sys.argv.(1)))) = 0 then ()
          with Failure "int_of_string" -> Format.printf "Invalid argument, give ONE positive integer without sign\n"
;;
main();;