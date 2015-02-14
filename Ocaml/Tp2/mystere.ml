let rec mystere n =
    match n with
    | _ when n > 100 ->
            failwith "Trop grand";
            Printf.printf "fantome"
    | _ -> mystere n
;;
