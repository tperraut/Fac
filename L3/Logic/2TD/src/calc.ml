open Printf
open Sys

type String tree = Empty | Noeud of String * String tree * String tree;;


let f b = if b then 1
else 0
;;

let x s =
  match s with
    | "0" -> false
    | _ -> true
;;

let imp a b = (not a) || b;;

let main () =
  let p = x argv.(1)  in
  let q = x argv.(2)  in
  let r = x argv.(3)  in
   print_string "f1={";
   print_int (f (p || q || (not r)));
   print_string ";";
   print_int (f ((not p) || q || (not r)));
   print_string ";";
   print_int (f (p || (not q) || r));
   print_string "}";
   print_string "\n";
   print_string "f2={";
   print_int (f (imp p (imp q p)));
   print_string ";";
   print_int (f (imp r (imp (imp r false) p)));
   print_string ";";
   print_int (f (imp (imp p (imp q r)) (imp (imp p q) (imp p r))));
   print_string "}";
   print_string "\n";
   print_string "f3={";
   print_int (f (imp p q));
   print_string ";";
   print_int (f (imp (imp p (imp (not q) r)) r));
   print_string ";";
   print_int (f (not r));
   print_string "}";
   print_string "\n"
;;
main ();;


