let ex1_mat =
    [|
                (*A;B;C;D;E;F;G*)
        (*A*)   [|false;false;false;true;true;false;false|];
        (*B*)   [|false;false;false;true;true;true;true|];
        (*C*)   [|false;false;false;false;true;false;true|];
        (*D*)   [|true;true;false;false;true;false;false|];
        (*E*)   [|true;true;true;true;false;true;true|];
        (*F*)   [|false;true;false;false;true;false;true|];
        (*G*)   [|false;true;true;false;true;true;false|]
    |]
;;
let ex2_mat =
    [|
                (*A;B;C;D;E;F;G;H*)
        (*A*)   [|false;true;true;true;false;false;true;true|];
        (*B*)   [|true;false;false;false;true;true;true;false|];
        (*C*)   [|true;false;false;true;false;true;true;true|];
        (*D*)   [|true;false;true;false;true;false;false;true|];
        (*E*)   [|false;true;false;true;false;true;true;false|];
        (*F*)   [|false;true;true;false;true;false;false;false|];
        (*G*)   [|true;true;true;false;true;false;true;false|];
        (*H*)   [|true;false;true;true;false;false;false;false|]
    |]
;;
let ex3_mat =
    [|
                (*1;2;3;4;5;6;7*)
        (*1*)   [|false;true;true;true;false;false;true|];
        (*2*)   [|true;false;true;true;true;false;true|];
        (*3*)   [|true;true;false;true;false;true;true|];
        (*4*)   [|true;true;true;false;true;true;false|];
        (*5*)   [|false;true;false;true;false;true;true|];
        (*6*)   [|false;false;true;true;true;false;true|];
        (*7*)   [|true;true;true;false;true;true;false|]
    |]
;;
let ex4_mat = [||];;
let count n boo = if boo then n + 1 else n;;
let counttrue mat = Array.fold_left (count) 0 mat;;
let deg_list mat =
    let len = Array.length mat in
    let rec makelist i li =
        if i = len then li
        else makelist (i + 1) ((i, counttrue mat.(i), 0)::li)
    in
    makelist 0 []
;;
let compare (_, x, _) (_, y, _) = y - x;;
let ex1_deg = List.sort compare (deg_list ex1_mat);;
let ex2_deg = List.sort compare (deg_list ex2_mat);;
let ex3_deg = List.sort compare (deg_list ex3_mat);;
(*DEBUG*)
let printsom (n, d, c) = Printf.printf "(N%d, D%d, C%d)" n d c; ();;
List.iter (printsom) ex1_deg;;
print_endline("");;
List.iter (printsom) ex2_deg;;
print_endline("");;
List.iter (printsom) ex3_deg;;
print_endline("");;
(*DEBUG*)

