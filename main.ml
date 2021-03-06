let parse () =
  let lexbuf = Lexing.from_channel stdin in
  try Parser.prog Lexer.token lexbuf
  with Parsing.Parse_error ->
    let i = lexbuf.Lexing.lex_start_p.Lexing.pos_cnum in
    failwith (Format.sprintf "Syntax error at char %i" i)

let eval ppf (e,v) = 
  Format.fprintf ppf "possible output:";
  try
    let v' = Mtt.eval e v in
    Format.fprintf ppf "%a@." Ta.print_v v';
  with Mtt.Error ->
    Format.fprintf ppf "Error@."

let infer ppf (e,t) = 
  let s = Mtt.infer Mtt.Env.empty e t () in
  Format.fprintf ppf "inferred input:%a@." Ta.print (Ta.normalize s)

let check ppf (e,t1,t2) = 
  let s = Mtt.infer Mtt.Env.empty e t2 () in
  try
    let v = Ta.sample (Ta.diff t1 s) in
    Format.fprintf ppf "check failed. Invalid input:%a@." Ta.print_v v;
    try
      let v' = Mtt.eval_avoid e v t2 in
      Format.fprintf ppf "Invalid output:%a@." Ta.print_v v';
    with Not_found -> Format.fprintf ppf "Couldn't find counter exemple.@."
  with Not_found -> Format.fprintf ppf "check passed.@."

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
