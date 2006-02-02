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

let sub dir n = match dir with Fst -> Ta.fst n | Snd -> Ta.snd n

type expr = {
  uid: int;
  mutable descr: expr_descr;
  mutable fv: VarSet.t option
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

let rec print_expr ppf e = match e.descr with
  | EVal _ -> Format.fprintf ppf "Val"
  | EElt _ -> Format.fprintf ppf "Elt"
  | ECopyTag (e1,e2) -> Format.fprintf ppf "CopyTag(%a,%a)" print_expr e1 print_expr e2
  | ECopy -> Format.fprintf ppf "Copy"
  | EVar _ -> Format.fprintf ppf "Var"
  | ELet (_,e) -> Format.fprintf ppf "Let(%a)" print_expr e
  | ELetN _ -> Format.fprintf ppf "LetN"
  | ECond (_,_,e1,e2) -> Format.fprintf ppf "Cond(%i,%i)" e1.uid e2.uid
  | ERand _ -> Format.fprintf ppf "Rand"
  | ESub _ -> Format.fprintf ppf "Sub"
  | ECompose _ -> Format.fprintf ppf "Compose"
  | EError -> Format.fprintf ppf "Error"

let iter_expr f e = match e.descr with
  | EVal _
  | ECopy
  | EVar _ 
  | ERand _ 
  | EError -> ()
  | ECond (e,_,e1,e2) -> f e; f e1; f e2
  | ESub (_,e) -> f e
  | EElt (_,e1,e2)
  | ECopyTag (e1,e2)
  | ECompose (e1,e2) -> f e1; f e2
  | ELet (binds,e2) 
  | ELetN (binds,e2) -> List.iter (fun (_,e) -> f e) binds; f e2

let iter_expr_deep f e =
  let seen = ref Pt.Set.empty in
  let rec aux e =
    if Pt.Set.mem e.uid !seen then ()
    else (seen := Pt.Set.add e.uid !seen; f e; iter_expr aux e)
  in
  aux e

let rec compute_fv seen e = match e.fv with Some fv -> fv | None ->
  let r = match e.descr with
    | EVar x -> VarSet.singleton x
    | ELet (binds,e2) 
    | ELetN (binds,e2) ->
	List.fold_left 
	  (fun accu (_,e) -> VarSet.union accu (compute_fv seen e)) 
	  (List.fold_left (fun accu (x,_) -> VarSet.remove x accu)
	     (compute_fv seen e2) binds)
	  binds
    | ESub (_,e) -> 
	if Pt.Set.mem e.uid seen then VarSet.empty else 
	  compute_fv (Pt.Set.add e.uid seen) e
    | _ ->
	let res = ref VarSet.empty in
	iter_expr
	  (fun e' -> res := VarSet.union (compute_fv seen e') !res) e;
	!res in
  if Pt.Set.is_empty seen then e.fv <- Some r;
  r

let fv e =
  match e.fv with
    | Some s -> s
    | None -> 
	let s = compute_fv Pt.Set.empty e in e.fv <- Some s; s
	   
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

let print_env ppf env =
  Env.iter (fun i (t,_) ->
	      Format.fprintf ppf "%s:%a@." (string_of_var i) Ta.print t)
    env

type 'a res = Type of 'a | Exn of exn

exception Refine of var * Ta.t

module Memo = Hashtbl.Make(Input)
let infer_memo = Memo.create 4096
let infer_stack = ref []

let nodes_memo : Ta.node res Memo.t = Memo.create 4096
let nodes_stack = ref []

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

let rec unstack' old = function
  | l when l == old -> ()
  | hd::tl -> 
      (try match Memo.find nodes_memo hd with
	 | Type n  when not (Ta.is_defined_node n) -> Memo.remove nodes_memo hd
	 | _ -> ()
       with Not_found -> ());
      unstack' old tl;
  | [] -> assert false

let checkpoint () =
  (!infer_stack,!nodes_stack)

let backtrack (old_stack,old_nodes) =
  unstack old_stack !infer_stack; 
  infer_stack := old_stack;
  unstack' old_nodes !nodes_stack; 
  nodes_stack := old_nodes



let rec infer env e t () =
  if Ta.is_empty t then Ta.empty
  else  
    let env = Env.restrict env (fv e) in
    assert(VarSet.subset (Env.domain env) (fv e));
    let i = (env,e.uid,t) in
    try 
      let r = 
	match Memo.find infer_memo i with Type t -> t | Exn exn -> raise exn
      in
      let r = 
	if is_empty r then Ta.empty 
	else if is_any r then Ta.any
	else if is_noneps r then Ta.noneps
	else if is_eps r then Ta.eps else r in
      Memo.replace infer_memo i (Type r);
      r
     
    with Not_found -> 
      try 
(*	Format.fprintf Format.std_formatter
	  "Begin infer for expr %i(%a), output %a@."
	  e.uid print_expr e
	  Ta.print t; *)
	let r = infer_descr env e t in 
	let r = 
	  if is_empty r then Ta.empty 
	  else if is_any r then Ta.any
	  else if is_noneps r then Ta.noneps
	  else if is_eps r then Ta.eps else r in
(*	Format.fprintf Format.std_formatter
	  "Infer for expr %i(%a), output %a%a===>%a-----------------@."
	  e.uid print_expr e
	  Ta.print t print_env env Ta.print r; *)
	Memo.replace infer_memo i (Type r);
	infer_stack := i :: !infer_stack;
	r
      with (Refine _) as exn ->
(*	Format.fprintf Format.std_formatter
	  "Infer for expr %i(%a), output %aFAILED@."
	  e.uid print_expr e
	  Ta.print t; *)
	Memo.replace infer_memo i (Exn exn);
	raise exn

and infer_descr env e t = match e.descr with
  | EVal v -> if Ta.is_in v t then Ta.any else Ta.empty
  | ECopy -> t
  | EVar x -> infer_var env x t
  | ERand t' -> if Ta.subset t' t then Ta.any else Ta.empty
  | ECond (e,t',e1,e2) -> infer_cond env e t' e1 e2 t
  | ECopyTag (e1,e2) -> infer_copytag env e1 e2 t
  | EElt (i,e1,e2) -> infer_elt env i e1 e2 t
  | ESub (dir,e) -> infer_sub env dir e t
  | ELet (binds,e2) -> infer_let env binds e2 t
  | ELetN (binds,e2) -> infer_letn env binds e2 t
  | ECompose (e1,e2) -> 
      let t1 = infer env e2 t () in
(*      let t1 = Ta.neg (Ta.normalize (Ta.neg t1)) in *)
      infer env e1 t1 ()
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
  let a = infer env e1 t () in
  if is_empty a then inter (infer env e2 t) (infer env e (Ta.neg t')) ()
  else let b = infer env e2 t () in
  if is_empty b then inter (infer env e1 t) (infer env e t') ()
  else
    if is_any (Ta.inter a b) then infer env e Ta.any ()
    else
      inter 
	(union (fun () -> b) (infer env e t'))
	(inter (union (fun () -> a) (infer env e (Ta.neg t')))
	   (infer env e Ta.any))
	() 

and infer_sub env dir e t =
  try
    let n = Memo.find nodes_memo (env,e.uid,t) in
    (match n with Exn exn -> raise exn | Type n -> sub dir n)
  with Not_found ->
    let n = Ta.mk () in
    Memo.add nodes_memo (env,e.uid,t) (Type n);
    nodes_stack := (env,e.uid,t) :: !nodes_stack;
(*    Format.fprintf Format.std_formatter "Create node %i for expr %i, dir %i, output type:%a" (Ta.uid n) e.uid (match dir with Fst -> 0 | Snd -> 1) Ta.print t; *)
    (try Ta.def n (infer env e t ())
     with exn -> Memo.replace nodes_memo (env,e.uid,t) (Exn exn); raise exn);
    sub dir n

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
  let ckpt = checkpoint () in
(*  Format.fprintf Format.std_formatter
    "Let %aoutput %a" print_env env' Ta.print t; *)
  match (try Type (infer env' e2 t ()) with exn -> Exn exn) with
    | Type t2 -> 
	let rec aux accu = function
	  | (x,e1)::rest ->
	      if is_any accu then Ta.any
	      else 
		let t' = infer env e1 (Ta.neg (fst (Env.find x env'))) () in
		aux (Ta.union accu t') rest
	  | [] -> accu in
	aux t2 binds

    | Exn (Refine (x,tx)) when List.mem_assq x binds ->
(*	Format.fprintf Format.std_formatter
	  "Refine %aCurrent %a---------@." Ta.print tx Ta.print (fst (Env.find x env')); *)
	backtrack ckpt;
	inter 
	  (infer_let_aux env binds 
	     (Env.change x (fun (t,_) -> (Ta.inter t tx, [])) env') e2 t)
	  (infer_let_aux env binds 
	     (Env.change x (fun (t,_) -> (Ta.diff t tx, [])) env') e2 t)
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
  let ckpt = checkpoint () in
  try infer env' e2 t ()
  with Refine (x,tx) when List.mem_assq x binds ->
    backtrack ckpt;

    let t1 = infer env (List.assq x binds) tx () in
    union
      (inter (fun () -> t1) 
	 (infer_letn_aux env binds 
	    (Env.change x (fun (t,neg) -> (Ta.inter t tx, neg)) env') e2
	    t))
      (inter (fun () -> Ta.neg t1) 
	 (infer_letn_aux env binds
	    (Env.change x (fun (t,neg) -> (t, List.sort Ta.compare (tx::neg))) env') e2
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
      (try Env.find x env
       with Not_found ->
	 raise Error)
  | ELet (binds,e2) | ELetN (binds,e2) ->
      let env' = 
	List.fold_left
	  (fun env' (x,e1) -> Env.add x (eval env e1 v) env')
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
	
let eval = eval Env.empty


let check_compose e =
  match e.descr with
    | ECompose (e1,e2) -> 
	(try 
(*	   if not (VarSet.is_empty (fv e2)) then raise Exit;*)
	   iter_expr_deep (fun e' -> if e == e' then raise Exit) e1
	 with Exit ->
	   Printf.eprintf "Ill-formed composition\n"; exit 1)
    | _ -> assert false
