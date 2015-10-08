let compte =
	let cpt = ref 0 in
	fun () -> incr cpt; !cpt
;;

