open Graphics;;

open_graph " 300x400";;

let rec push x y r =
    let event = wait_next_event [Button_down] in
    let mx = event.mouse_x in
    let my = event.mouse_y in
    if (mx - x) * (mx - x) + (my - y) * (my - y) < r * r then
        begin
            set_color red;
            fill_circle x y r
        end
    else
        push x y r
;;

let rec jeu () =
    let event = wait_next_event [Mouse_motion] in
    let mx = event.mouse_x in
    let my = event.mouse_y in
    if push 100 100 10 then
        Format.printf "%d %d@." mx my
    else
        jeu()
;;


    fill_circle 100 100 10 ;;
jeu () ;;
