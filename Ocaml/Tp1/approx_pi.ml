
let n = int_of_string Sys.argv.(1);;

let approx_pi p cpt =
  if cpt=0 then 4. *. (float_of_int p) /. (float_of_int n)
  else
    let x = Random.float 1. in
    let y = Random.float 1. in
    let c = if x*.x +. y*.y < 1. then 1 else 0 in
    approx_pi (p+c) (cpt-1);
;;

Printf.printf "%f\n" (approx_pi 0 n);;

