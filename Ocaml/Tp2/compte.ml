let rec compte i n =
    match i with
    |0 -> ()
    |_ -> print_int (n + 1 - i); compte (i - 1) n
;;
compte 10 10 ;;
