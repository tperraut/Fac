let couper l =
  let rec coupe l (l1, l2) =
    match l with
      | [] -> (l1, l2)
      | [x] -> (x::l1, l2)
      | x::y::s -> coupe s (x::l1, y::l2)
  in
    coupe l ([], [])
;;

let couper2 l =
  let rec coupe l (l1, l2) =
    match l with
      | [] -> (l1, l2)
      | x::s ->
          let l1 = x::l1 in
            coupe s (l2, l1)
  in
    coupe l ([], [])
;;

let couper3 l =
  List.fold_left (fun (l1, l2) x -> (l2, x::l1)) ([],[]) l
;;

let affiche_int_list l =
  let rec affiche l =
    match l with
      | [] -> print_string "]"
      | x::s ->
          print_string " ";
          print_int x ;
          print_string " ";
          affiche s
  in
    print_string "[";
    affiche l;
    print_string "\n"
;;

let l = [2; 4; 12; 0; 8];;

let (x, y) = couper3 l;;

print_string "L1 = ";;
affiche_int_list x;;

print_string "L2 = ";;
affiche_int_list y;;

let fusion comp l1 l2 =
  let rec f (l1, l2) l =
    match l1,l2 with
      | [], s
      | s, [] -> List.rev_append l s
      | x1::s1, x2::s2 ->
          if comp x1 x2 < 0
          then f (s1, l2) (x1::l)
          else f (l1, s2) (x2::l)
  in
    f (l1, l2) []
;;

print_string "La fusion de L1 et L2 :  ";;
let ll = fusion compare x y;;
affiche_int_list (ll);;

let rec trier comp l =
  match l with
    | [] -> []
    | [_] -> l
    | _ ->
        let l1, l2 = couper l in
          fusion comp (trier comp l1) (trier comp l2)
;;

let llt = trier compare ll;;
affiche_int_list (llt);;

let make_list n =
  Random.self_init ();
  let rec doit acc l =
        match acc with
          | 0 -> l
          | _ -> doit (acc - 1) (Random.int(n - 1)::l)
  in
    doit n []
;;
let lr = make_list 10;;
affiche_int_list (lr);;

let numerotation l =
  let (ll, _) =
    List.fold_left (fun (l, cpt) x -> ((x, cpt)::l, cpt + 1)) ([], 0) l in
    List.rev ll
;;

let comp_assoc (x1, _) (x2, _) =
  compare x1 x2
;;

let affiche_pint_list l =
  begin
    print_string "[";
    List.iter (fun (a, b) -> Format.printf "(%d, %d)@." a b) l;
    print_string "]";
    print_string "\n"
  end
;;

let lrn = numerotation lr;;
affiche_pint_list lrn;;
