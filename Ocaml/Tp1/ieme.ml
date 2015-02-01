print_string "Entrez une phrase : " ;;
let bob = read_line () ;;
print_string "Entrez un nombre : " ;;
let i = read_int() ;;
if i > 0 && i < String.length bob then
    Printf.printf ("%c\n") (String.get bob (i - 1))
else
    print_string "Valeur de i invalide\n"
;;
