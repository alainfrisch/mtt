type var = int
module VarSet = Pt.Set
module Env = Pt.Map

type dir = Fst | Snd

type expr =
  | EVal of Ta.v
  | EPair of expr * expr
  | ECopy
  | EVar of var
  | ELet of var * expr * expr
  | ECond of expr * Ta.t * expr * expr
  | ERand of Ta.t
  | ESub of int * dir * expr ref * Ta.v

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

let union f1 f2 () =
  let t1 = f1 () in
  if Ta.is_trivially_any t1 then Ta.any else Ta.union t1 (f2 ())

let inter f1 f2 () =
  let t1 = f1 () in
  if Ta.is_trivially_empty t1 then Ta.empty else Ta.inter t1 (f2 ())

let rec unstack tr = function
  | hd::tl when hd == tr -> tl
  | hd::tl -> Memo.remove infer_memo hd; unstack tr tl
  | [] -> assert false

let rec infer env e t () = 
  if Ta.is_empty t then Ta.empty
  else if Ta.is_empty (Ta.neg t) then Ta.any
  else
  match e with
  | EVal v -> if Ta.is_in v t then Ta.any else Ta.empty
  | ECopy -> t
  | EVar x ->
      let tx = 
	try Env.find x env
	with Not_found -> Printf.eprintf "Unbound variable %i\n" x; exit 1 in
      if Ta.subset tx t then Ta.any
      else if Ta.disjoint t tx then Ta.empty
      else raise (Refine (x,t))
  | ERand t' -> if Ta.subset t' t then Ta.any else Ta.empty
  | ECond (e,t',e1,e2) ->
      inter 
	(union (infer env e t') (infer env e2 t))
	(union (infer env e (Ta.neg t')) (infer env e1 t))
	()
  | EPair (e1,e2) ->
      (try List.fold_left
	 (fun accu (t1,t2) ->
	    if Ta.is_empty t1 || Ta.is_empty t2 then accu
	    else
	      let r = 
		union 
		  (infer env e1 (Ta.neg t1)) 
		  (infer env e2 (Ta.neg t2)) () in
	      let accu = Ta.inter accu r in
	      if Ta.is_trivially_empty accu then raise Exit else accu)
	 Ta.any
	 (Ta.dnf_neg_pair t)
       with Exit -> Ta.empty)
  | ESub (uid,dir,e,v) -> infer_sub env uid dir !e v t
  | ELet (x,e1,e2) -> infer_let env x e1 e2 Ta.any t ()

and infer_sub env uid dir e v t =
  let i = (env,uid,t) in
  try match Memo.find infer_memo i with Type t -> t | Exn exn -> raise exn
  with Not_found ->
    let d = Ta.mk () in
    let r = 
      (match dir with Fst -> Ta.fst | Snd -> Ta.snd) (Ta.get_delayed d) in
    let r = if Ta.is_in v t then Ta.union r Ta.any_atom else r in
    Memo.add infer_memo i (Type r);
    infer_stack := i :: !infer_stack;
    (try Ta.def d (infer env e t ())
     with exn ->
       Memo.replace infer_memo i (Exn exn);
       infer_stack := unstack i !infer_stack;
       raise exn);
     r

and infer_let env x e1 e2 dom t () =
  try union (infer env e1 (Ta.neg dom)) (infer (Env.add x dom env) e2 t) ()
  with Refine (y,tx) when x == y ->
    inter 
      (infer_let env x e1 e2 (Ta.inter dom tx) t)
      (infer_let env x e1 e2 (Ta.diff dom tx) t)
      ()
