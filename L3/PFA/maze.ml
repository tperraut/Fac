open Graphics

(* union - find *)

type t = {
  rank : int array;
  parent : int array;
}

let create n =
  { rank = Array.create n 0;
    parent = Array.init n (fun i -> i) }

let rec find t i =
  let p = t.parent.(i) in
  if p = i then
    i
  else begin
    let r = find t p in
    t.parent.(i) <- r;
    r
  end

let union t i j =
  let ri = find t i in
  let rj = find t j in
  if ri <> rj then begin
    if t.rank.(ri) < t.rank.(rj) then
      t.parent.(ri) <- rj
    else begin
      t.parent.(rj) <- ri;
      if t.rank.(ri) = t.rank.(rj) then 
        t.rank.(ri) <- t.rank.(ri) + 1
    end
  end

(* Knuth shuffle *)

let knuth_shuffle t =
  for j = Array.length t - 1 downto 1 do
    let k = Random.int (j+1) in
    let v = t.(j) in t.(j) <- t.(k); t.(k) <- v
  done


(* labyrinthe *)

let () = Random.self_init ()
let n = 30
let gr i = 600 * i / n

let () = 
  open_graph " 600x600";
  for i = 0 to n do
    moveto (gr i) 0; lineto (gr i) 600;
    moveto 0 (gr i); lineto 600 (gr i)
  done

let edges = 
  let l = ref [] in
  for i = 0 to n-1 do 
    for j = 0 to n-1 do
      if i < n-1 then l := ((i, j), (i+1, j)) :: !l;
      if j < n-1 then l := ((i, j), (i, j+1)) :: !l
    done; 
  done;
  Array.of_list !l

let () = knuth_shuffle edges
let u = create (n * n)

let () =
  set_color white;
  let f ((i, j), (i', j')) =
    let k = i * n + j in
    let k' = i' * n + j' in
    if find u k <> find u k' then begin
      moveto (gr i') (gr (j')) ; 
      lineto (gr (i+1)) (gr (j+1)) ;
      union u k k';
    end
  in
  Array.iter f edges

let () = ignore (read_key ())
