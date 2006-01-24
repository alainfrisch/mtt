let parse () =
  let lexbuf = Lexing.from_channel stdin in
  try Parser.prog Lexer.token lexbuf
  with Parsing.Parse_error ->
    let i = lexbuf.Lexing.lex_start_p.Lexing.pos_cnum in
    failwith (Format.sprintf "Syntax error at char %i" i)

let eval ppf (e,v) = 
  Format.fprintf ppf "possible output:%a@." Ta.print_v (Mtt.eval e v)

let infer ppf (e,t) = 
  let s = Mtt.infer Mtt.Env.empty e t () in
  Printf.eprintf "Inferred\n"; flush stderr;
(*  let s = Ta.normalize s in  *)
(*  let s = Ta.normalize2 s in
  Printf.eprintf "Normalized\n"; flush stderr; *)
  Format.fprintf ppf "inferred input:%a@." Ta.print s 

let check ppf (e,t1,t2) = 
  let s = Mtt.infer Mtt.Env.empty e t2 () in
  Format.fprintf ppf "Inferred@.";
(*  Format.fprintf ppf "%a@." Ta.print (Ta.normalize s); *)
(*  Format.fprintf ppf "Sample:%a@." Ta.print_v (Ta.sample s); *)
  if Ta.subset t1 s then 
    Format.fprintf ppf "check passed.@."
  else (
    Format.fprintf ppf "check failed, looking for sample...@."; flush stderr;
    try
      let v = Ta.sample (Ta.diff t1 s) in
      Format.fprintf ppf "%a@." Ta.print_v v;
      Format.fprintf ppf "possible output:%a@." Ta.print_v (Mtt.eval e v)
    with Not_found -> assert false)

let ppf = Format.std_formatter

let main () =
  let prog = Syntax.parse (parse ()) in
  List.iter (function 
	       | `Check x -> check ppf x 
	       | `Infer x -> infer ppf x
	       | `Eval x -> eval ppf x
	    ) prog

let () = 
  try main ()
  with exn -> Printf.eprintf "Error:\n%s\n" (Printexc.to_string exn); exit 2
