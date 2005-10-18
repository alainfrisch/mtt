type 'a _var = { mutable level: int; mutable unique: 'a }
type 'a _node = 
  | Zero 
  | One 
  | Var of 'a _var * 'a _node * 'a _node * 'a _node * int

type 'a _node_var = 
    { mutable v: 'a _var; 
      mutable p: 'a _node; 
      mutable n: 'a _node; 
      mutable inv: 'a _node;
      mutable uid: int }

let uid = function Zero -> 0 | One -> 1 | Var (_,_,_,_,id) -> id


module rec Unique : Weak.S with type data = Unique.t _node_var = 
  Weak.Make(struct
	      type t = Unique.t _node_var
	      let hash n = uid n.p + 17 * uid n.n
	      let equal n1 n2 = n1.p == n2.p && n1.p == n2.p
	    end)

type node = Unique.t _node
type node_var = Unique.t _node_var
type var = Unique.t _var

let node_of_node_var : node_var -> node = Obj.magic

let cur_uid = ref 0

let inv = function
  | Zero -> One
  | One -> Zero
  | Var (_,_,_,n,_) -> n

let make_node var pos neg =
  Printf.printf "make_node!\n"; flush stdout;
  if pos == neg then pos
  else (
    let n = { v=var; p=pos; n=neg; inv=Zero; uid=0 } in
    let n' = Unique.merge var.unique n in
    if n == n' then (
      n.uid <- !cur_uid; 
      incr cur_uid;
      let ninv = { v=var; p=inv pos; n=inv neg; 
	  inv=node_of_node_var n; uid = !cur_uid } in
      n.inv <- node_of_node_var ninv;
      incr cur_uid;
      Unique.add var.unique ninv;
    );
    node_of_node_var n'
  )

let swap_node nod v1 v2 =
  let pp,pn =
    match nod.p with
      | Var (v,pp,pn,_,_) when v == v2 -> pp,pn
      | p -> p,p
  and np,nn =
    match nod.n with
      | Var (v,np,nn,_,_) when v == v2 -> np,nn
      | n -> n,n
  in
  if (pp == pn) && (np == nn) then
    Unique.add v1.unique nod
  else (
    nod.v <- v2;
    nod.p <- make_node v1 pp np;
    nod.n <- make_node v1 pn nn;
    Unique.add v2.unique nod
  )

let swap_variables v1 v2 =
  let l1 = v1.level in
  v1.level <- v2.level;
  v2.level <- l1;

  let all1 = v1.unique in
  v1.unique <- Unique.create 32;
  Unique.iter (fun n -> swap_node n v1 v2) all1


let max_level = ref 0

let new_var () =
  incr max_level;
  { level = !max_level; unique = Unique.create 32 }

let and_cache_len = 10000
let and_cache_res = Weak.create and_cache_len
let and_cache_arg1 = Array.create and_cache_len (-1)
let and_cache_arg2 = Array.create and_cache_len (-1)

let rec _and nod1 nod2 =
  if nod1 == nod2 then nod1
  else match nod1,nod2 with
    | Zero,_ | _,Zero -> Zero
    | One,nod | nod,One -> nod
    | Var (v1,p1,n1,inv1,id1), Var (v2,p2,n2,_,id2) ->
	if inv1 == nod2 then Zero
	else let h = abs ((id1 * 257 + id2) mod and_cache_len) in
	let r = 
	  if (and_cache_arg1.(h) == id1) && (and_cache_arg2.(h) == id2)
	  then Weak.get and_cache_res h 
	  else (and_cache_arg1.(h) <- id1; and_cache_arg2.(h) <- id2; None)
	in match r with
	  | Some res -> res
	  | None ->
	      let l1 = v1.level and l2 = v2.level in
	      let res = 
		if l1 == l2 then make_node v1 (_and p1 p2) (_and n1 n2)
		else if l1 < l2 then make_node v1 (_and p1 nod2) (_and n1 nod2)
		else make_node v2 (_and p2 nod1) (_and n2 nod1)
	      in
	      Weak.set and_cache_res h (Some res);
	      res

let _or nod1 nod2 = inv (_and (inv nod1) (inv nod2))
let _diff nod1 nod2 = _and nod1 (inv nod2)
		
let var v = make_node v One Zero
