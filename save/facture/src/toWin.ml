open Printf
open Sys

let rec rw ic oc =
  try let s = input_line ic in
    fprintf oc "%s\r\n" s;
    rw ic oc
  with e -> printf "Done"
;;

let f argv =
  let f = argv.(1) in
    try
      let ic = open_in f in
      let oc = open_out_gen [Open_append; Open_creat] 0o666 ("W_" ^ f) in
        rw ic oc;
        close_in ic;
        close_out oc
    with e -> printf "Bad file"
;;

let main () =
  let ac = Array.length argv in
    match ac with
      | 2 -> f argv
      | _ -> printf "Invalid argument\n"
;;
main ();;
