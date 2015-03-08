open Graphics;;

open_graph " 300x400";;

let rec push x y r =
  let event = wait_next_event [Button_down] in
  let mx = event.mouse_x in
  let my = event.mouse_y in
    if (mx - x) * (mx - x) + (my - y) * (my - y) < r * r then
      begin
        set_color red;
        fill_circle x y r;
        drag x y x y r
      end
    else
      push x y r
and drag x y mx my r =
  let event = wait_next_event [Mouse_motion;Button_up] in
    if event.button == false then
      begin
        Format.printf "%d %d@." mx my;
        push x y r
      end
    else
      let mx = event.mouse_x in
      let my = event.mouse_y in
        clear_graph ();
        fill_circle mx my r;
        drag mx my mx my r
;;

fill_circle 100 100 10 ;;
drag 100 100 100 100 10 ;;
