let result = 0 ;;
let roll () = Random.int 5 ;;
let yorn n =
    (
        Printf.printf "Vous avez fait %d, rejouer? y/n" dice
        let s = read_line () in
        if String.get s 0 == 'y' then true
        else false;
    )
;;
let rec play () =
    let dice = roll () in
    if dice != 4 && dice != 5 then dice + 1
    else
        if yorn dice then dice + 1 + play ()
        else dice + 1;
;;
