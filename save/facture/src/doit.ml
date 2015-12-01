open Printf
open Sys

let fos s = float_of_string s;;
let month s =
  match s with
    | "Septembre" -> "09"
    | "Octobre" -> "10"
    | "Novembre" -> "11"
    | "Decembre" -> "12"
    | "Janvier" -> "01"
    | "Fevrier" -> "02"
    | "Mars" -> "03"
    | "Avril" -> "04"
    | "Mai" -> "05"
    | "Juin" -> "06"
    | "Juillet" -> "07"
    | "Aout" -> "08"
    | _ -> ""
;;

let rec hours f h =
  try let s = input_line f in
    hours f (h +. (float_of_string (String.sub s 12 3)))
  with e ->
    match e with 
      | Failure "float_of_string" -> hours f (h)
      | _ -> h
;;

let total f =
  try
    let ic = open_in f in
    let oc = open_out_gen [Open_append; Open_creat] 644 f in
    let h = hours ic 0. in
      fprintf oc "------------------------\n";
      if h > 10. then
        fprintf oc "| TOTAL  | %.1f|  %.1f|\n" h (h *. 15.)
      else
        fprintf oc "| TOTAL  |  %.1f|  %.1f|\n" h (h *. 15.);
      fprintf oc "------------------------\n";
      close_in ic;
      close_out oc
  with e -> printf "Bad filename\n"
;;

let add a1 a2 a3 =
  let len = String.length a1 in
    try
      let oc = open_out_gen [Open_append; Open_creat] 644 a1 in
      let tm = Unix.gmtime (Unix.time ()) in
      let year = tm.Unix.tm_year in
        fprintf oc "|%s/%s/%d|  %.1f|   %.1f|\n" a2
          (month (String.sub a1 0 (len - 4))) (year - 100)
          (fos a3) ((fos a3) *. 15.);
        close_out oc
    with e -> printf "Bad filename\n"
;;

let main () =
  let ac = Array.length argv in
    match ac with
      | 3 when argv.(1) = "-t" ->
          total argv.(2)

      | _ when ac < 4 -> printf "Too few arguments\nGive FILENAME DAY HOURS\n"
      | _ when ac > 4 -> printf "Too many arguments\nGive FILENAME DAY HOURS\n"
      | _ -> add argv.(1) argv.(2) argv.(3)
;;
main();;
