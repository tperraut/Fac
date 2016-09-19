open Format
open Lexing
open Error

let usage = "usage: compilo [options] file.ml"

let interpret  = ref false
let compile    = ref true

let spec = [ "-i", Arg.Tuple [Arg.Set interpret; Arg.Clear compile],
	     "  interpreter only";
	   ]

let file, filer = 
  let file = ref None in
  let set_file s =  
    if not (Filename.check_suffix s ".ml") then 
      raise (Arg.Bad "no .ml extension");
    file := Some s
  in
  Arg.parse spec set_file usage;
  match !file with
    | Some f ->
      let csf = Filename.chop_extension f in
      let res = Printf.sprintf "%s.mips" csf in
      f, res
    | None -> Arg.usage spec usage; exit 1

let () =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  try
    let e = Parser.toplevel_expr Lexer.token lb in
    close_in c;
    if   !interpret
    then let n = Interpreter.interpret_expr e in
	 Printf.printf "%d\n" n
    else ();
    if !compile
    then Compiler.compile_toplevel_expr e
    else ();
    exit 0
  with
    | Error.Error (e,p) ->
      Error.print err_formatter file e p;
      exit 1
    | e ->
	eprintf "Anomaly: %s\n@." (Printexc.to_string e);
      exit 2
