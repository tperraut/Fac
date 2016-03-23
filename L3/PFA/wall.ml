(* Table de hachage *)

type ('a, 'b) t = {
  mutable size : int;
  buckets : ('a * 'b) list array;
  }
    
let array_length = 5003      
  
let create () = { size = 0; buckets = Array.create array_length [] }
  
let cardinal h = h.size
  
let find x h =
  let i = (Hashtbl.hash x) mod array_length in
  let rec lookup = function
    | [] -> raise Not_found
    | (k, v) :: _ when x = k -> v
    | _ :: b -> lookup b
  in
  lookup h.buckets.(i)
    
let mem_bucket x = List.exists (fun (y, _) -> x = y)
  
let add x v h =
  let i = (Hashtbl.hash x) mod array_length in
  let b = h.buckets.(i) in 
  if not (mem_bucket x b) then begin
    h.size <- h.size + 1;
    h.buckets.(i) <- (x, v) :: b
  end
    
let remove x h =
  let i = (Hashtbl.hash x) mod array_length in
  let b = h.buckets.(i) in
  if mem_bucket x b then begin
    h.size <- h.size - 1;
    h.buckets.(i) <- List.filter (fun (y, _) -> y<>x) b
  end


(* Mur de briques *)

let width = 32
let height = 10

let add2 r = (r lsl 2) lor 0b10
let add3 r = (r lsl 3) lor 0b100

let rec rows n = 
  if n <= 1 then []
  else if n = 2 || n = 3 then [0]
  else 
    let r1 = rows (n-2) in
    let r2 = rows (n-3) in
    let l1 = List.map add2 r1 in
    let l2 = List.map add3 r2 in
    l1 @ l2

let rows = rows 32

let sum f l = List.fold_left (fun acc x -> Int64.add (f x) acc) 0L l

(* version 1 *)


let rec w (r, h) = 
  if h  = 1 then 1L
  else sum (fun r' -> if r land r' = 0 then w (r', h - 1) else 0L) rows

let sol = sum (fun r -> w (r, height)) rows
let () = Format.printf "%Ld@." sol


(* version 2 *)


let table = create ()

let rec w (r, h) = 
  if h  = 1 then 1L
  else 
    sum (fun r' -> if r land r' = 0 then memo_w (r', h - 1) else 0L) rows

and memo_w w (r, h) =
  try  find (r, h) table 
  with Not_found -> let v = w (r, h) in add (r,h) v table; v

let sol = sum (fun r -> w (r, height)) rows
let () = Format.printf "%Ld@." sol


(* version 3 *)


let memo ff =
  let h = create () in
  let rec f x = 
    try find x h
    with Not_found -> let v = ff f x in add x v h; v 
  in 
  f

let w = 
  memo (fun  w (r, h) ->
    if h  = 1 then 1L
    else 
      sum (fun r' -> if r land r' = 0 then w (r', h - 1) else 0L) rows)



let sol = sum (fun r -> w (r, height)) rows
let () = Format.printf "%Ld@." sol


