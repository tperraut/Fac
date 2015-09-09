let result = 0 ;;
let roll () = Random.int 5 ;;
let yorn (n) =
    Printf.printf "Vous avez fait %d, rejouer? y/n    " (n+1);
    let s = read_line () in
    if String.get s 0 == 'y' then true
    else false;
;;
let rec play (r) =
    let dice = roll () in
    let r = r + dice + 1 in
    if dice != 4 && dice != 5 then
        begin
            Printf.printf "Votre score est de : %d\n" r;
            Printf.printf "Vous avez fait : %d\n" (dice + 1);
            dice + 1
        end
    else
        begin
            Printf.printf "Votre score est de : %d\n" r;
            if yorn (dice) then
                dice + 1 + play (r)
            else dice + 1
        end
;;
let _ = play(result) ;;
