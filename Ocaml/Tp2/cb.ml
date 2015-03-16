open Graphics;;

let left = 0.;;
let right = 300.;;
let down = 0.;;
let up = 500.;;
type vector = {
  vx: float;
  vy: float;
};;
type ball = {
  x: float;
  y: float;
  r: int;
};;
type paddle = {
  px: float;
  py: float;
  w: float;
  h: float;
};;
let iof x = int_of_float x;;
let foi x = float_of_int x;;
let initv () = {vx = (Random.float 1.); vy = (Random.float 1.)};;
open_graph(" " ^ string_of_float(right) ^ string_of_float(up));;
(*auto_synchronize(false);;*)
let draw_ball b =
  set_color blue;
  fill_circle (iof(b.x)) (iof(b.y)) b.r
;;
let new_position b v = {
  x = b.x +. v.vx *. b.x;
  y = b.y +. v.vy *. b.y;
  r = b.r
};;
let draw_paddle p =
  set_color black;
  fill_rect (iof(p.px)) (iof(p.py)) (iof(p.w)) (iof(p.h))
;;
let rec bounce b v =
  let bb = new_position b v in
    if bb.y > up || bb.y < down then
      let vv = {vx = v.vx; vy = -. v.vy} in
        bounce b vv
        else
          if bb.x < left || bb.x > right then
            let vv = {vx = -. v.vx; vy = v.vy} in
              vv
              else
                v
;;
let v = initv ();;
let b = {x = 10.; y = 30.; r = 5};;
let rec play b v =
  let event = wait_next_event [Mouse_motion] in
  let mx = event.mouse_x in
  let my = event.mouse_y in
  let vv = bounce b v in
  let bb = new_position b vv in
    Format.printf "%d %d@." mx my;
    (*clear_graph ();*)
    draw_ball bb;
    if mx > 0 && mx < 290 then
      begin
        let p = {px = foi(mx); py = 20.; w = 10.; h = 4.} in
          draw_paddle p;
          play bb v;
      end
    else
      play bb v
;;
draw_ball b;;
play b v;;
