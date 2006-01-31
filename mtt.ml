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
  | ELet of (var * expr) list  * expr
  | ELetN of (var * expr) list * expr
  | ECond of expr * Ta.t * expr * expr
  | ERand of Ta.t
  | ESub of dir * expr
  | ECompose of expr * expr
  | EError

module Input = struct
  type t = (Ta.t * Ta.t list) Env.t * int * Ta.t


  let rec hash_ta_list accu = function
    | [] -> accu 
    | hd::tl -> hash_ta_list (Ta.hash hd + accu * 257) tl

  let hash_x (t,tl) = 
    hash_ta_list (Ta.hash t) tl
      
  let rec equal_ta_list l1 l2 = match (l1,l2) with
    | hd1::tl1, hd2::tl2 when Ta.equal hd1 hd2 -> equal_ta_list tl1 tl2
    | [], [] -> true
    | _ -> false

  let equal_x (t1,tl1) (t2,tl2) =
    Ta.equal t1 t2 && equal_ta_list tl1 tl2

  let hash (env,e,t) =
    (Env.hash hash_x env) + (257 * e) + 65537 * (Ta.hash t)
  let equal (env1,e1,t1) (env2,e2,t2) =
    (e1 == e2) && (Env.equal equal_x env1 env2) && (Ta.equal t1 t2)
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

let is_eps t =
  try Ta.is_equal t Ta.eps
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
	 | Type t when not (Ta.is_defined t) -> Memo.remove infer_memo hd
	 | _ -> ()
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
	  else if is_noneps r then Ta.noneps
	  else if is_eps r then Ta.eps else r in
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
  | ELet (binds,e2) -> infer_let env binds e2 t
  | ELetN (binds,e2) -> infer_letn env binds e2 t
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
  let (pos,neg) = 
    try Env.find x env
    with Not_found -> 
      Printf.eprintf "Unbound variable %s\n" (string_of_var x); exit 1 in

  if Ta.subset pos t then Ta.any
  else 
    let tx = Ta.inter pos t in
    if Ta.is_empty tx || (List.exists (fun n -> Ta.subset tx n) neg)
    then Ta.empty
    else raise (Refine (x,t))

and infer_cond env e t' e1 e2 t =
  inter (infer env e Ta.any)
    (inter 
       (union (infer env e t') (infer env e2 t))
       (union (infer env e (Ta.neg t')) (infer env e1 t)))
    () 

and infer_sub env idx dir e t =
  let n = Ta.mk () in
(*  Format.fprintf Format.std_formatter "Create node %i for expr %i, dir %i, output type:%a" (Ta.uid n) e.uid (match dir with Fst -> 0 | Snd -> 1) Ta.print t; *)
  let r = match dir with Fst -> Ta.fst n | Snd -> Ta.snd n in
  Memo.replace infer_memo idx (Type r);
  Ta.def n (infer env e t ());
  r

and infer_let env binds e2 t =
  let rec aux t1 env' = function
    | [] -> Ta.inter t1 (infer_let_aux env binds env' e2 t ())
    | (x,e1)::rest ->
	let env' = Env.add x (Ta.any,[]) env' 
	and t1 = Ta.inter t1 (infer env e1 Ta.any ()) in
	if is_empty t1 then Ta.empty else aux t1 env' rest
  in
  aux Ta.any env binds
  
and infer_let_aux env binds env' e2 t () =
  let old_stack = !infer_stack in
  match (try Type (infer env' e2 t ()) with exn -> Exn exn) with
    | Type t2 -> 
	let rec aux accu = function
	  | (x,e1)::rest ->
	      if is_any accu then Ta.any
	      else 
		let t' = infer env e1 (Ta.neg (fst (Pt.Map.find x env'))) () in
		aux (Ta.union accu t') rest
	  | [] -> accu in
	aux t2 binds

    | Exn (Refine (x,tx)) when List.mem_assq x binds ->
	unstack old_stack !infer_stack; 
	infer_stack := old_stack;
	inter 
	  (infer_let_aux env binds 
	     (Pt.Map.change x (fun (t,_) -> (Ta.inter t tx, [])) env') e2 t)
	  (infer_let_aux env binds 
	     (Pt.Map.change x (fun (t,_) -> (Ta.diff t tx, [])) env') e2 t)
	  ()
    | Exn exn -> raise exn

and infer_letn env binds e2 t =
  let rec aux t1 env' = function
    | [] -> Ta.inter t1 (infer_letn_aux env binds env' e2 t ())
    | (x,e1)::rest ->
	let env' = Env.add x (Ta.any,[]) env' 
	and t1 = Ta.inter t1 (infer env e1 Ta.any ()) in
	if is_empty t1 then Ta.empty else aux t1 env' rest
  in
  aux Ta.any env binds
  
and infer_letn_aux env binds env' e2 t () =
  let old_stack = !infer_stack in
  try infer env' e2 t ()
  with Refine (x,tx) when List.mem_assq x binds ->
    unstack old_stack !infer_stack; 
    infer_stack := old_stack;

    let t1 = infer env (List.assq x binds) tx () in
    union
      (inter (fun () -> t1) 
	 (infer_letn_aux env binds 
	    (Pt.Map.change x (fun (t,neg) -> (Ta.inter t tx, neg)) env') e2
	    t))
      (inter (fun () -> Ta.neg t1) 
	 (infer_letn_aux env binds
	    (Pt.Map.change x (fun (t,neg) -> (t, List.sort Ta.compare (tx::neg))) env') e2
	    t))
      ()

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
  | ELet (binds,e2) | ELetN (binds,e2) ->
      let env' = 
	List.fold_left
	  (fun env' (x,e1) -> Pt.Map.add x (eval env e1 v) env')
	  env
	  binds in
      eval env' e2 v
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
	    | ECompose (e1,e2) -> aux e1; aux e2
	    | ELet (binds,e2) 
	    | ELetN (binds,e2) -> List.iter (fun (_,e) -> aux e) binds; aux e2)
  in
  match e.descr with
    | ECompose (e1,e2) -> 
	(try aux e2
	 with Exit ->
	   Printf.eprintf "Ill-formed composition\n"; exit 1)
    | _ -> assert false
