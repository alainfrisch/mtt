module Type = struct
  type t =
    | Ident of string
    | Eps
    | Elt of string * t * t
    | And of t * t
    | Or of t * t
    | Diff of t * t
end

module Expr = struct
  type t =
    | Ident of string
    | Random of Type.t
    | Var of string
    | Let of string * t * t
    | Left of t
    | Right of t
    | Cond of t * Type.t * t * t
    | Eps
    | Elt of string * t * t
    | CopyTag of t * t
    | Compose of t * t
end

module Phrase = struct
  type t =
    | Type of string * Type.t
    | Expr of string * Expr.t
    | Infer of Expr.t * Type.t
    | Check of Expr.t * Type.t * Type.t
    | Eval of Expr.t * Expr.t
end

let parse prog =
  let types = Hashtbl.create 256 in
  let exprs = Hashtbl.create 256 in

  let vars = Hashtbl.create 256 in
  let var_id = ref 0 in
  
  let parse_var x =
    try Hashtbl.find vars x
    with Not_found ->
      incr var_id;
      Hashtbl.add vars x !var_id;
      !var_id in

  let type_nodes = Hashtbl.create 256 in

  let rec parse_type g = function
    | Type.Ident "Any" -> Ta.any
    | Type.Ident "Empty" -> Ta.empty
    | Type.Ident x when List.mem x g ->
	Printf.eprintf "Unguarded recursion on type %s\n" x; exit 1
    | Type.Ident x when not (Hashtbl.mem types x) ->
	Printf.eprintf "Cannot resolve type %s\n" x; exit 1
    | Type.Ident x -> parse_type (x::g) (Hashtbl.find types x)
    | Type.Eps -> Ta.eps
    | Type.Elt (x,t1,t2) ->
	Ta.elt (Ta.atom_of_string x) (parse_type_node t1) (parse_type_node t2)
    | Type.And (t1,t2) -> Ta.inter (parse_type g t1) (parse_type g t2)
    | Type.Or (t1,t2) -> Ta.union (parse_type g t1) (parse_type g t2)
    | Type.Diff (t1,t2) -> Ta.diff (parse_type g t1) (parse_type g t2)
  and parse_type_node e =
    try Hashtbl.find type_nodes e
    with Not_found ->
      let n = Ta.mk () in
      Hashtbl.add type_nodes e n;
      Ta.def n (parse_type [] e);
      n in

  let expr_nodes = Hashtbl.create 256 in
  let expr_id = ref 0 in
  let composes = ref [] in

  let ex d = incr expr_id; { Mtt.uid = !expr_id; Mtt.descr = d } in
  let ecopy = ex Mtt.ECopy in
  let eeps = ex (Mtt.EVal Ta.Eps) in
  let rec parse_expr g = function
    | Expr.Ident "Copy" -> ecopy
    | Expr.Ident x when List.mem x g ->
	Printf.eprintf "Unguarded recursion on expression %s\n" x; exit 1
    | Expr.Ident x when not (Hashtbl.mem exprs x) ->
	Printf.eprintf "Cannot resolve expression %s\n" x; exit 1
    | Expr.Ident x -> parse_expr (x::g) (Hashtbl.find exprs x)
    | Expr.Eps -> eeps
    | Expr.Elt (x,e1,e2) -> 
	ex (Mtt.EElt (Ta.atom_of_string x, parse_expr g e1, parse_expr g e2))
    | Expr.CopyTag (e1,e2) -> 
	ex (Mtt.ECopyTag (parse_expr g e1, parse_expr g e2))
    | Expr.Var x -> ex (Mtt.EVar (parse_var x))
    | Expr.Random t -> 
	let t = parse_type [] t in
	if Ta.is_empty t then
	  (Printf.eprintf "Cannot rand(_) an empty type\n"; exit 1);
	ex (Mtt.ERand t)
    | Expr.Let (x,e1,e2) -> 
	ex (Mtt.ELet (parse_var x, parse_expr g e1, parse_expr g e2))
    | Expr.Left e -> 
	ex (Mtt.ESub (Mtt.Fst, parse_expr_node e))
    | Expr.Right e -> 
	ex (Mtt.ESub (Mtt.Snd, parse_expr_node e))
    | Expr.Cond (e,t,e1,e2) ->
	ex (Mtt.ECond (parse_expr g e, parse_type [] t,
		       parse_expr g e1, parse_expr g e2))
    | Expr.Compose (e1,e2) ->
	let r = ex (Mtt.ECompose (parse_expr g e1, parse_expr g e2)) in
	composes := r :: !composes;
	r

  and parse_expr_node e =
    try Hashtbl.find expr_nodes e
    with Not_found ->
      let n = ex Mtt.ECopy in
      Hashtbl.add expr_nodes e n;
      n.Mtt.descr <- (parse_expr [] e).Mtt.descr;
      n
  in

  let parse_val e =
    let rec aux e = match e.Mtt.descr with
      | Mtt.EVal v -> v
      | Mtt.EElt (i,e1,e2) -> Ta.Elt (i, aux e1, aux e2)
      | _ -> 
	  (Printf.eprintf "Not a value\n"; exit 1);
    in
    aux (parse_expr [] e)
  in


  let cmds = ref [] in
  List.iter 
    (function 
       | Phrase.Type (x,t) -> Hashtbl.add types x t
       | Phrase.Expr (x,e) -> Hashtbl.add exprs x e
       | Phrase.Infer (e,t) -> cmds := `Infer (e,t) :: !cmds
       | Phrase.Check (e,t1,t2) -> cmds := `Check (e,t1,t2) :: !cmds
       | Phrase.Eval (e1,e2) -> cmds := `Eval (e1,e2) :: !cmds) prog;
  let p = 
    List.rev_map 
      (function
	 | `Infer (e,t) -> 
	     `Infer (parse_expr [] e, parse_type [] t)
	 | `Check (e,t1,t2) -> 
	     `Check (parse_expr [] e, parse_type [] t1, parse_type [] t2)
	 | `Eval (e1,e2) ->
	     `Eval (parse_expr [] e1, parse_val e2)
      ) !cmds in
  List.iter
    Mtt.check_compose
    !composes;
  p
