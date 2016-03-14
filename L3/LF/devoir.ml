type exp =
    | Empty
    | Epsilon
    | Char of char
    | Or of exp * exp
    | Concat of exp * exp
    | Star of exp
;;

let rec contient_epsilon = function
    | Empty -> false
    | Char(c) -> false
    | Or(r1, r2) -> contient_epsilon r1 || contient_epsilon r2
    | Concat(r1, r2) -> contient_epsilon r1 && contient_epsilon r2
    | _ -> true
;;

let residu r c =
    match r with
    | Empty -> Empty
    | Char(x) when x = c -> Epsilon
    | Char(x) -> Empty
    | Or(r1, r2) -> Or((residu r1 c), (residu r2 c))
    | Concat(r1, _) -> residu r1 c
    | Star(r1) -> 
;;

let rec reconnait r w =
    match w with
    | [] -> true
    | c::s -> reconnait (residu c r) s
;;
