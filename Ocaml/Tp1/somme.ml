let somme_2 x y = x + y ;;
let rec somme_n n =
    if n > 0 then n + somme_n (n - 1) else 0
;;
let rec fibo n =
    if n >= 0 && n <= 1 then n
    else
        fibo (n - 2) + fibo (n - 1)
;;
print_int (fibo 1) ;;
print_char '\n' ;;
print_int (fibo 2) ;;
print_char '\n' ;;
print_int (fibo 5) ;;
print_char '\n' ;;
