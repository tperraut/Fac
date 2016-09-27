open Format
open Lexing

let usage = "usage: compilo [options] file.ml"

let interpret  = ref false
let compile    = ref true

let spec = [ "-i", Arg.Tuple [Arg.Set interpret; Arg.Clear compile],
             "  interpreter only";
]

let file = 
  let file = ref None in
  let set_file s =  
    if not (Filename.check_suffix s ".ml") then 
      raise (Arg.Bad "no .ml extension");
    file := Some s
  in
    Arg.parse spec set_file usage;
    match !file with Some f -> f | None -> Arg.usage spec usage; exit 1

let () =
  let c = open_in file in
  let lb = Lexing.from_channel c in
    try
      let e = Parser.toplevel_expr Lexer.token lb in
        close_in c;
        if   !interpret
        then
          begin
            let v = Interpreter.interpret_expr e in
              match v with
                | Interpreter.Int n         -> Printf.printf "%d\n" n
                | Interpreter.Bool b when b -> Printf.printf "%d\n" 1
                | Interpreter.Bool b        -> Printf.printf "%d\n" 0
          end
        else ();
        if !compile
        then Compiler.compile_toplevel_expr e;
        exit 0
    with
        e ->
          eprintf "Anomaly: %s\n@." (Printexc.to_string e);
          exit 2
