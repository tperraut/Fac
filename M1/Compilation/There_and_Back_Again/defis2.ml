open Printf
open Ast

let rpar (o1 : binop) (o2 : binop) : bool =
  match o1, o2 with
    | Mult, Plus
    | Mult, Minus
    | Minus, Plus
    | Minus, Minus
    | Div, _ -> true
    |_ -> false

let lpar (o1 : binop) (o2 : binop) : bool =
  match o1, o2 with
    | Plus, Mult
    | Plus, Div
    | Minus, Mult
    | Minus, Div -> true
    | _ -> false

let op_toString (op : binop) : string =
  match op with
    | Mult -> " * "
    | Div -> " / "
    | Plus -> " + "
    | Minus -> " - "

let pretty_print (e : expr) : unit =
  match e with
    | Eint(x) -> printf "%d" x
    | Ebinop(op, e1, e2) ->
        let rec pprint (e : expr) (o : binop) (sag : bool) : unit =
          (*sag definie si e est dans un sous arbre gauche ou droit*)
          match e, sag with
            | Eint(x), _ -> printf "%d" x
            | Ebinop(op, e1, e2), true when lpar op o ->
                printf "(";
                pprint e1 op true;
                printf "%s" (op_toString op);
                pprint e2 op false;
                printf ")"
            | Ebinop(op, e1, e2), false when rpar o op ->
                printf "(";
                pprint e1 op true;
                printf "%s" (op_toString op);
                pprint e2 op false;
                printf ")"
            | Ebinop(op, e1, e2), _->
                pprint e1 op true;
                printf "%s" (op_toString op);
                pprint e2 op false;
        in
          pprint e1 op true;
          printf "%s" (op_toString op);
          pprint e2 op false
