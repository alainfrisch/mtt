let parse () =
  let lexbuf = Lexing.from_channel stdin in
  try Parser.prog Lexer.token lexbuf
  with Parsing.Parse_error ->
    let i = lexbuf.Lexing.lex_start_p.Lexing.pos_cnum in
    failwith (Format.sprintf "Syntax error at char %i" i)

let infer ppf (e,t) = 
  let s = Mtt.infer Mtt.Env.empty e t () in
(*  Printf.eprintf "Inferred\n"; flush stderr; *)
  let s = Ta.normalize s in 
(*  Printf.eprintf "Normalized\n"; flush stderr; *)
(*  let s = Ta.normalize2 s in
  Printf.eprintf "Normalized\n"; flush stderr; *)
  Format.fprintf ppf "inferred input:%a@." Ta.print s

let check ppf (e,t1,t2) = 
  let s = Mtt.infer Mtt.Env.empty e t2 () in
  try
    let v = Ta.sample (Ta.diff t1 s) in
    Format.fprintf ppf "check failed, sample:%a@." Ta.print_v v
  with Not_found ->
    Format.fprintf ppf "check passed.@."

let ppf = Format.std_formatter

let main () =
  let prog = Syntax.parse (parse ()) in
  List.iter (function `Check x -> check ppf x | `Infer x -> infer ppf x) prog

let () = 
  try main ()
  with exn -> Printf.eprintf "Error:\n%s\n" (Printexc.to_string exn); exit 2
