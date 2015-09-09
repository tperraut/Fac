type tache = {
	priorite : int;
	demandeur : string;
	demandes_nombres : (string * int) list;
}
let rec map f l new =
	match l with
	 | [] -> new
	 | x::s -> map f s ((f (x))::s)
;;
let mix l1 l2 l3 =
  let l1len = List.length l1 in
  if l1len != List.length l2 || l1len != List.length l3 then failwith "l1 l2 et l3 n'ont pas la meme taille"; []
  let nd = List.map (fun x -> ())
;;