type exp =
    | Empty
    | Epsilon
    | Char of char
    | Or of exp * exp
    | Concat of exp * exp
    | Star of exp
;;

let rec contient_epsilon = function
    | Empty | Char (_) -> false
    | Or (r1, r2) -> contient_epsilon r1 || contient_epsilon r2
    | Concat (r1, r2) -> contient_epsilon r1 && contient_epsilon r2
    | _ -> true (* Star ou Epsilon *)
;;

let rec residu r c =
    match r with
    | Char (x) when x = c -> Epsilon
    | Or (r1, r2) -> Or ((residu r1 c), (residu r2 c))
    | Concat (r1, r2) when contient_epsilon r1 -> Or (Concat (residu r1 c, r2), residu r2 c)
    | Concat (r1, r2) -> Concat (residu r1 c, r2)
    | Star (r1) -> Concat (residu r1 c, Star (r1))
    | _ -> Empty (* Empty ou Epsilon ou Char(x) avec x != c *)
;;

let rec reconnait r w =
    match w with
    | [] -> contient_epsilon r
    | c::s -> reconnait (residu r c) s
;;

let rec string_of_exp e =
    match e with
    | Empty -> "Ø"
    | Epsilon -> "ε"
    | Char (c) -> ""^(String.make 1 c)
    | Or (e1, e2) -> "("^(string_of_exp e1)^"|"^(string_of_exp e2)^")"
    | Concat (e1, e2) -> "("^(string_of_exp e1)^"."^(string_of_exp e2)^")"
    | Star e1 -> "("^(string_of_exp e1)^")*"
;;

(*test*)
let l = Concat(Star(Or(Char('a'), Char('b'))),Char('a'));;
print_string((string_of_exp (residu l ('a')))^"\n");;
print_string((string_of_exp (residu l ('b')))^"\n");;
if reconnait l (['a';'b';'a';'b';'a';'b';'a';'b';'a';'b';'a']) then print_string("OK\n")
