module Type = struct
  type t =
    | Ident of string
    | Int of int
    | Tag of string
    | Pair of t * t
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
    | Int of int
    | Tag of string
    | Left of t
    | Right of t
    | Cond of t * Type.t * t * t
    | Pair of t * t
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
    | Type.Ident "Pair" -> Ta.any_pair
    | Type.Ident "Atom" -> Ta.any_atom
    | Type.Ident x when List.mem x g ->
	Printf.eprintf "Unguarded recursion on type %s\n" x; exit 1
    | Type.Ident x when not (Hashtbl.mem types x) ->
	Printf.eprintf "Cannot resolve type %s\n" x; exit 1
    | Type.Ident x -> parse_type (x::g) (Hashtbl.find types x)
    | Type.Int n -> Ta.atom n
    | Type.Tag s -> Ta.atom (Ta.atom_of_string s)
    | Type.Pair (t1,t2) ->
	Ta.inter (Ta.fst (parse_type_node t1)) (Ta.snd (parse_type_node t2))
    | Type.And (t1,t2) -> Ta.inter (parse_type g t1) (parse_type g t2)
    | Type.Or (t1,t2) -> Ta.union (parse_type g t1) (parse_type g t2)
    | Type.Diff (t1,t2) -> Ta.diff (parse_type g t1) (parse_type g t2)
  and parse_type_node e =
    try Hashtbl.find type_nodes e
    with Not_found ->
      let n = Ta.mk () in
      let t = Ta.get_delayed n in
      Hashtbl.add type_nodes e t;
      Ta.def n (parse_type [] e);
      t in

  let expr_nodes = Hashtbl.create 256 in
  let expr_id = ref 0 in

  let rec parse_expr g = function
    | Expr.Ident "Copy" -> Mtt.ECopy
    | Expr.Ident x when List.mem x g ->
	Printf.eprintf "Unguarded recursion on expression %s\n" x; exit 1
    | Expr.Ident x when not (Hashtbl.mem exprs x) ->
	Printf.eprintf "Cannot resolve expression %s\n" x; exit 1
    | Expr.Ident x -> parse_expr (x::g) (Hashtbl.find exprs x)
    | Expr.Int n -> Mtt.EVal (Ta.Atom n)
    | Expr.Tag s -> Mtt.EVal (Ta.Atom (Ta.atom_of_string s))
    | Expr.Pair (e1,e2) -> Mtt.EPair (parse_expr g e1, parse_expr g e2)
    | Expr.Var x -> Mtt.EVar (parse_var x)
    | Expr.Random t -> 
	let t = parse_type [] t in
	if Ta.is_empty t then
	  (Printf.eprintf "Cannot rand(_) an empty type\n"; exit 1);
	Mtt.ERand t
    | Expr.Let (x,e1,e2) -> 
	Mtt.ELet (parse_var x, parse_expr g e1, parse_expr g e2)
    | Expr.Left e -> 
	Mtt.ESub ((incr expr_id; !expr_id), Mtt.Fst, parse_expr_node e,
		 Ta.Atom 0)
    | Expr.Right e -> 
	Mtt.ESub ((incr expr_id; !expr_id), Mtt.Snd, parse_expr_node e,
		 Ta.Atom 0)
    | Expr.Cond (e,t,e1,e2) ->
	Mtt.ECond (parse_expr g e, parse_type [] t,
		   parse_expr g e1, parse_expr g e2)
  and parse_expr_node e =
    try Hashtbl.find expr_nodes e
    with Not_found ->
      let n = ref Mtt.ECopy in
      Hashtbl.add expr_nodes e n;
      n := parse_expr [] e;
      n
  in

  let parse_val e =
    let rec aux = function
      | Mtt.EVal v -> v
      | Mtt.EPair (e1,e2) -> Ta.Pair (aux e1, aux e2)
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
  List.rev_map 
    (function
       | `Infer (e,t) -> 
	   `Infer (parse_expr [] e, parse_type [] t)
       | `Check (e,t1,t2) -> 
	   `Check (parse_expr [] e, parse_type [] t1, parse_type [] t2)
       | `Eval (e1,e2) ->
	   `Eval (parse_expr [] e1, parse_val e2)
    ) !cmds
