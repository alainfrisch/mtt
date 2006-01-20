let parse () =
  let lexbuf = Lexing.from_channel stdin in
  try Parser.prog Lexer.token lexbuf
  with Parsing.Parse_error ->
    let i = lexbuf.Lexing.lex_start_p.Lexing.pos_cnum in
    failwith (Format.sprintf "Syntax error at char %i" i)

let infer (e,t) = 
  let s = Mtt.infer Mtt.Env.empty e t () in
(*  Printf.eprintf "Inferred\n"; flush stderr; *)
  let s = Ta.normalize s in
(*  Printf.eprintf "Normalized\n"; flush stderr; *)
(*  let s = Ta.normalize2 s in
  Printf.eprintf "Normalized\n"; flush stderr; *)
  Format.fprintf Format.std_formatter "inferred input:%a@." Ta.print s

let check (e,t1,t2) = 
  let s = Mtt.infer Mtt.Env.empty e t2 () in
  let b = Ta.subset t1 s in
  Format.fprintf Format.std_formatter "check:%b@." b

let main () =
  let prog = Syntax.parse (parse ()) in
  List.iter (function `Check x -> check x | `Infer x -> infer x) prog

let () = 
  try main ()
  with exn -> Printf.eprintf "Error:\n%s\n" (Printexc.to_string exn); exit 2
