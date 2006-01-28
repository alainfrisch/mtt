type var = int
module VarSet = Pt.Set
module Env = Pt.Map

let vars = Hashtbl.create 256
let inv_vars = Hashtbl.create 256
let var_id = ref 0

let var_of_string x =
  try Hashtbl.find vars x
  with Not_found ->
    incr var_id;
    Hashtbl.add vars x !var_id;
    Hashtbl.add inv_vars !var_id x;
    !var_id
  
let string_of_var i =
  Hashtbl.find inv_vars i

type dir = Fst | Snd

type expr = {
  uid: int;
  mutable descr: expr_descr;
}
and expr_descr =
  | EVal of Ta.v
  | EElt of Ta.atom * expr * expr
  | ECopyTag of expr * expr
  | ECopy
  | EVar of var
  | ELet of var * expr * expr
  | ECond of expr * Ta.t * expr * expr
  | ERand of Ta.t
  | ESub of dir * expr
  | ECompose of expr * expr
  | EError

module Input = struct
  type t = Ta.t Env.t * int * Ta.t

  let hash (env,e,t) =
    (Env.hash Ta.hash env) + (257 * e) + 65537 * (Ta.hash t)
  let equal (env1,e1,t1) (env2,e2,t2) =
    (e1 == e2) && (Env.equal Ta.equal env1 env2) && (Ta.equal t1 t2)
end

type res = Type of Ta.t | Exn of exn

exception Refine of var * Ta.t

module Memo = Hashtbl.Make(Input)
let infer_memo = Memo.create 4096
let infer_stack = ref []

let is_empty t =
  try Ta.is_empty t
  with Ta.Undefined -> false

let is_any t =
  try Ta.is_any t
  with Ta.Undefined -> false

let is_noneps t =
  try Ta.is_equal t Ta.noneps
  with Ta.Undefined -> false


let union f1 f2 () =
  let t1 = f1 () in
  if is_any t1 then Ta.any else Ta.union t1 (f2 ())

let inter f1 f2 () =
  let t1 = f1 () in
  if is_empty t1 then Ta.empty else Ta.inter t1 (f2 ())

let rec unstack old = function
  | l when l == old -> ()
  | hd::tl -> 
      (try match Memo.find infer_memo hd with
	 | Exn _ -> ()
	 | Type _ ->  Memo.remove infer_memo hd
       with Not_found -> ());
      unstack old tl;
  | [] -> assert false

let rec infer env e t () =
  if Ta.is_empty t then Ta.empty
  else  
    let i = (env,e.uid,t) in
    try match Memo.find infer_memo i with Type t -> t | Exn exn -> raise exn
    with Not_found -> 
      try 
	let r = infer_descr env i e t in 
	let r = 
	  if is_empty r then Ta.empty 
	  else if is_any r then Ta.any
	  else if is_noneps r then Ta.noneps else r in
	Memo.replace infer_memo i (Type r);
	infer_stack := i :: !infer_stack;
	r
      with (Refine _) as exn ->
	Memo.replace infer_memo i (Exn exn);
	raise exn

and infer_descr env uid e t = match e.descr with
  | EVal v -> if Ta.is_in v t then Ta.any else Ta.empty
  | ECopy -> t
  | EVar x -> infer_var env x t
  | ERand t' -> if Ta.subset t' t then Ta.any else Ta.empty
  | ECond (e,t',e1,e2) -> infer_cond env e t' e1 e2 t
  | ECopyTag (e1,e2) -> infer_copytag env e1 e2 t
  | EElt (i,e1,e2) -> infer_elt env i e1 e2 t
  | ESub (dir,e) -> infer_sub env uid dir e t
  | ELet (x,e1,e2) -> 
      inter (infer env e1 Ta.any) (infer_let env x e1 e2 Ta.any t) ()
  | ECompose (e1,e2) -> infer env e1 (infer env e2 t ()) ()
  | EError -> Ta.empty

and infer_elt_aux b env e1 e2 = 
  List.fold_left
    (fun accu (t1,t2) ->
       let r = 
	 union 
	   (infer env e1 (Ta.neg t1)) 
	   (infer env e2 (Ta.neg t2)) () in
       let accu = Ta.inter accu (Ta.union b r) in
       if Ta.is_trivially_empty accu then raise Exit else accu)
    
and infer_elt env i e1 e2 t =
  let accu = inter (infer env e1 Ta.any) (infer env e2 Ta.any) () in
  try infer_elt_aux Ta.empty env e1 e2 accu (Ta.dnf_neg_pair i t)
  with Exit -> Ta.empty
    
and infer_copytag env e1 e2 t =
  let accu = 
    inter 
      (inter (fun () -> Ta.noneps) (infer env e1 Ta.any))
      (infer env e2 Ta.any)
      () in
  let dom,tr_def,tr = Ta.dnf_neg_all t in
  try
    let accu = infer_elt_aux (Ta.tag_in dom) env e1 e2 accu tr_def in
    List.fold_left 
      (fun accu (i,x) -> infer_elt_aux (Ta.nottag i) env e1 e2 accu x) accu tr
  with Exit -> Ta.empty

and infer_var env x t =
  let tx = 
    try Env.find x env
    with Not_found -> 
      Printf.eprintf "Unbound variable %s\n" (string_of_var x); exit 1 in
  if Ta.subset tx t then Ta.any
  else if Ta.disjoint t tx then Ta.empty
  else raise (Refine (x,t))

and infer_cond env e t' e1 e2 t =
  inter (infer env e Ta.any)
    (inter 
       (union (infer env e t') (infer env e2 t))
       (union (infer env e (Ta.neg t')) (infer env e1 t)))
    () 

and infer_sub env idx dir e t =
  let n = Ta.mk () in
  let r = match dir with Fst -> Ta.fst n | Snd -> Ta.snd n in
  Memo.replace infer_memo idx (Type r);
  Ta.def n (infer env e t ());
  r

and infer_let env x e1 e2 dom t () =
  let old_stack = !infer_stack in
  match (try Type (infer (Env.add x dom env) e2 t ()) 
	 with exn -> Exn exn) with
    | Type t2 -> union (fun () -> t2) (infer env e1 (Ta.neg dom)) ()
    | Exn (Refine (y,tx)) when x == y ->
	unstack old_stack !infer_stack; 
	infer_stack := old_stack;
	inter 
	  (infer_let env x e1 e2 (Ta.inter dom tx) t)
	  (infer_let env x e1 e2 (Ta.diff dom tx) t)
	  ()
    | Exn exn -> raise exn

exception Error

let rec eval env e v = match e.descr with
  | EVal v' -> v'
  | EElt (i,e1,e2) -> Ta.Elt (i,eval env e1 v, eval env e2 v)
  | ECopyTag (e1,e2) ->
      (match v with
	 | Ta.Eps -> raise Error
	 | Ta.Elt (i,_,_) -> Ta.Elt (i, eval env e1 v, eval env e2 v))
  | ECopy -> v
  | EVar x -> 
      (try Pt.Map.find x env
       with Not_found ->
	 raise Error)
  | ELet (x,e1,e2) -> eval (Pt.Map.add x (eval env e1 v) env) e2 v
  | ECond (e,t,e1,e2) ->
      eval env (if Ta.is_in (eval env e v) t then e1 else e2) v
  | ERand t -> Ta.sample t
  | ESub (dir,e) ->
      (match v with
	 | Ta.Eps -> raise Error
	 | Ta.Elt (i,v1,v2) -> eval env e (if dir = Fst then v1 else v2))
  | ECompose (e1,e2) -> eval env e2 (eval env e1 v)
  | EError -> raise Error
	
let eval = eval Pt.Map.empty


let check_compose e =
  let seen = ref Pt.Set.empty in
  let rec aux e' =
    if e' == e then raise Exit;
    if Pt.Set.mem e'.uid !seen then ()
    else (seen := Pt.Set.add e'.uid !seen;
	  match e'.descr with
	    | EVal _
	    | ECopy
	    | EVar _ 
	    | ERand _ 
	    | EError -> ()
	    | ECond (e,_,e1,e2) -> aux e; aux e1; aux e2
	    | ESub (_,e) -> aux e
	    | EElt (_,e1,e2)
	    | ECopyTag (e1,e2)
	    | ELet (_,e1,e2)
	    | ECompose (e1,e2) -> aux e1; aux e2)
  in
  match e.descr with
    | ECompose (e1,e2) -> 
	(try aux e2
	 with Exit ->
	   Printf.eprintf "Ill-formed composition\n"; exit 1)
    | _ -> assert false
