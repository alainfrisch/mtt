module Type = struct
  type t =
    | Ident of string
    | Eps
    | Elt of string * t
    | AnyElt of t
    | Alt of t * t
    | Seq of t * t
    | Star of t
    | Plus of t
    | And of t * t
    | Diff of t * t
end

module Expr = struct
  type t =
    | Call of string * t list
    | Random of Type.t
    | Var of string
    | Let of (string * t) list * t
    | LetN of (string * t) list * t
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
    | Expr of string * string list * Expr.t
    | Infer of Expr.t * Type.t
    | Check of Expr.t * Type.t * Type.t
    | Eval of Expr.t
end

module E = struct
  include Ta
    
  type elt =
    | Tag of int * Ta.node
    | Any of Ta.node
	
  let elt e q2 = match e with
    | Tag (i,q1) -> elt i q1 q2
    | Any q1 -> anyelt q1 q2

  let equal e1 e2 = match (e1,e2) with
    | Tag (a1,n1), Tag (a2,n2) -> a1 == a2 && n1 == n2
    | Any n1, Any n2 -> n1 == n2
    | _, _ -> false

  let hash = function
    | Tag (a,n) -> a + 257 * (uid n)
    | Any n -> 65537 * (uid n)
end

module ReComp = Regexp.Compile(E)

let parse prog =
  let types = Hashtbl.create 256 in
  let exprs = Hashtbl.create 256 in

  let type_nodes = Hashtbl.create 256 in

  let rec parse_regexp g = function
    | Type.Ident "Any" -> Regexp.Any
    | Type.Ident x when List.mem x g ->
	Printf.eprintf "Unguarded recursion on type %s\n" x; exit 1
    | Type.Ident x when not (Hashtbl.mem types x) ->
	Printf.eprintf "Cannot resolve type %s\n" x; exit 1
    | Type.Ident x -> parse_regexp (x::g) (Hashtbl.find types x)
    | Type.Eps -> Regexp.Eps
    | Type.Elt (x,t1) -> 
	Regexp.Elem (E.Tag (Ta.atom_of_string x, parse_type_node t1))
    | Type.AnyElt t1 ->
	Regexp.Elem (E.Any (parse_type_node t1))
    | Type.Seq (t1,t2) ->
	Regexp.Seq (parse_regexp g t1, parse_regexp g t2)
    | Type.Alt (t1,t2) ->
	Regexp.Alt (parse_regexp g t1, parse_regexp g t2)
    | Type.Star t1 ->
	Regexp.Star (parse_regexp g t1)
    | Type.Plus t1 ->
	Regexp.Plus (parse_regexp g t1)
    | Type.And _
    | Type.Diff _ ->
	Printf.eprintf "Operator cannot be used within regular expression";
	exit 1

  and parse_type_node e =
    try Hashtbl.find type_nodes e
    with Not_found ->
      let n = Ta.mk () in
      Hashtbl.add type_nodes e n;
      Ta.def n (parse_type [] e);
      n

  and parse_type g = function
    | Type.Ident "Any" -> Ta.any
    | Type.Ident "Empty" -> Ta.empty
    | Type.Ident x when List.mem x g ->
	Printf.eprintf "Unguarded recursion on type %s\n" x; exit 1
    | Type.Ident x when not (Hashtbl.mem types x) ->
	Printf.eprintf "Cannot resolve type %s\n" x; exit 1
    | Type.Ident x -> parse_type (x::g) (Hashtbl.find types x)
    | Type.Alt (t1,t2) -> Ta.union (parse_type g t1) (parse_type g t2)
    | Type.And (t1,t2) -> Ta.inter (parse_type g t1) (parse_type g t2)
    | Type.Diff (t1,t2) -> Ta.diff (parse_type g t1) (parse_type g t2)
    | t -> ReComp.compile (parse_regexp g t) in

  let exprs_nodes = Hashtbl.create 256 in
  let expr_id = ref 0 in
  let composes = ref [] in
  let loops = ref [] in

  let ex d = 
    incr expr_id; { Mtt.uid = !expr_id; Mtt.descr = d; Mtt.fv = None } in

  (* TODO: check well-formedness of expressions. *)
  let rec parse_expr e =
    try Hashtbl.find exprs_nodes e
    with Not_found ->
      let n = ex Mtt.ECopy in
      loops := n :: !loops;
      Hashtbl.add exprs_nodes e n;
      let d = parse_expr_descr [] e in
      n.Mtt.descr <- d;
      (match d with Mtt.ECompose _ -> composes := n :: !composes | _ -> ());
      n
  and parse_expr_descr g = function
    | Expr.Call ("Copy",[]) -> Mtt.ECopy
    | Expr.Call ("Error",[]) -> Mtt.EError
    | Expr.Call (x,_) when List.mem x g ->
	Printf.eprintf "Unguarded recursion on expression %s\n" x; exit 1
    | Expr.Call (x,_) when not (Hashtbl.mem exprs x) ->
	Printf.eprintf "Cannot resolve expression %s\n" x; exit 1
    | Expr.Call (x,args) -> 
	let (params,body) = Hashtbl.find exprs x in
	if List.length params != List.length args then
	  (Printf.eprintf "Arity mismatch on call to %s\n" x; exit 1);
	if params == [] then parse_expr_descr (x::g) body
	else
	  let binds = List.map2 (fun x e -> (x,parse_expr e)) params args in
	  Mtt.ELet (binds, parse_expr body)
    | Expr.Eps -> Mtt.EVal Ta.Eps
    | Expr.Elt (x,e1, e2) -> 
	Mtt.EElt (Ta.atom_of_string x, parse_expr e1, parse_expr e2)
    | Expr.CopyTag (e1, e2) -> 
	Mtt.ECopyTag (parse_expr e1, parse_expr e2)
    | Expr.Var x -> Mtt.EVar (Mtt.var_of_string x)
    | Expr.Random t -> 
	let t = parse_type [] t in
	if Ta.is_empty t then
	  (Printf.eprintf "Cannot rand(_) an empty type\n"; exit 1);
	Mtt.ERand t
    | Expr.Let (binds,e2) -> 
	Mtt.ELet (parse_bindings binds, parse_expr e2)
    | Expr.LetN (binds,e2) -> 
	Mtt.ELetN (parse_bindings binds, parse_expr e2)
    | Expr.Left e -> 
	Mtt.ESub (Mtt.Fst, parse_expr_node e)
    | Expr.Right e -> 
	Mtt.ESub (Mtt.Snd, parse_expr_node e)
    | Expr.Cond (e,t,e1,e2) ->
	Mtt.ECond (parse_expr e, parse_type [] t,
		       parse_expr e1, parse_expr e2)
    | Expr.Compose (e1,e2) ->
	Mtt.ECompose (parse_expr e1, parse_expr e2)

  and parse_bindings binds =
    List.map (fun (x,e) -> Mtt.var_of_string x, parse_expr e) binds

  and parse_expr_node e =
    parse_expr e
  in

  let cmds = ref [] in
  List.iter 
    (function 
       | Phrase.Type (x,t) -> Hashtbl.add types x t
       | Phrase.Expr (x,args,e) -> 
	   Hashtbl.add exprs x (List.map Mtt.var_of_string args, e)
       | Phrase.Infer (e,t) -> cmds := `Infer (e,t) :: !cmds
       | Phrase.Check (e,t1,t2) -> cmds := `Check (e,t1,t2) :: !cmds
       | Phrase.Eval e1 -> cmds := `Eval e1 :: !cmds) prog;
  let p = 
    List.rev_map 
      (function
	 | `Infer (e,t) -> 
	     `Infer (parse_expr e, parse_type [] t)
	 | `Check (e,t1,t2) -> 
	     `Check (parse_expr e, parse_type [] t1, parse_type [] t2)
	 | `Eval e1 ->
	     `Eval (parse_expr e1, Ta.Eps)
      ) !cmds in
  List.iter Mtt.check_wf !loops;
  List.iter Mtt.check_compose !composes;
  p
