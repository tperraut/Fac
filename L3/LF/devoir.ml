type exp =
    | Empty
    | Epsilon
    | Char of char
    | Or of exp * exp
    | Concat of exp * exp
    | Star of exp
;;

let rec contient_epsilon = function
    | Empty || Char(c) -> false
    | Or(r1, r2) -> contient_epsilon r1 || contient_epsilon r2
    | Concat(r1, r2) -> contient_epsilon r1 && contient_epsilon r2
    | _ -> true (*Star ou Epsilon*)
;;

let rec residu r c =
    match r with
    | Char(x) when x = c -> Epsilon
    | Empty || Epsilon || Char(x) -> Empty
    | Or(r1, r2) -> Or((residu r1 c), (residu r2 c))
    | Concat(r1, r2) when r1 != Epsilon -> Concat((residu r1 c), r2)
    | Concat (_, r2) -> residu r2 c
    | Star(r1) -> Star((residu r1 c))
;;

let rec reconnait r w =
    match w with
    | [] -> true
    | c::s -> reconnait (residu c r) s
;;
