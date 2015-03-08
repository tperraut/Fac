let rec decompte n =
  match n with
    |0 -> ()
    |_ -> print_int n; decompte (n - 1)
;;
decompte 10 ;;
