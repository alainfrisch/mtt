module type HashedOrdered = sig
  type t
  val equal: t -> t -> bool
  val hash: t -> int
  val compare: t -> t -> int
end

module type S = sig
  type var
    (** Type of atoms. *)

  include HashedOrdered (* Formulas. *)

  val dump: 
    (Format.formatter -> var -> unit) -> Format.formatter -> t -> unit

  val uid: t -> int
    (** Returns an integer which uniquely identifies the formula. *)

  val one: t
    (** The true formula. *)

  val zero: t
    (** The false formula. *)

  val (!!!): var -> t
    (** Builds a formula from an atom. *)

  val (~~~): t -> t
    (** Logical negation. *)

  val (&&&): t -> t -> t
    (** Logical conjunction. *)

  val (|||): t -> t -> t
    (** Logical disjunction. *)

  val (---): t -> t -> t
    (** Logical difference. *)

  val simpl: t -> t -> t
    (** [simpl t1 t2] returns a formula [t] which is equivalent to [t1]
	for valuations such that [t2] hold. *)

  val dnf: t -> (var list * var list) list
    (** [dnf t] puts the formula [t] is disjunctive normal form
	(disjunction of conjunctions of atoms and negation of atoms. *)

  val dnf_enum :
    ('a -> 'b -> 'b) ->
    pos:(var -> 'a -> 'a) -> neg:(var -> 'a -> 'a) -> 'b -> 'a -> t -> 'b
end

module Make(X : HashedOrdered) : S with type var = X.t = struct

  type var = X.t

  type t = 
    | Zero 
    | One 
    | Var of X.t * t * t * t * int

  type t_var = 
      { mutable v: X.t; 
	mutable p: t; 
	mutable n: t; 
	mutable inv: t;
	mutable uid: int;
      }
	
  let uid = function Zero -> 0 | One -> 1 | Var (_,_,_,_,id) -> id
    
    
  module Unique : Weak.S with type data = t_var = 
    Weak.Make(
      struct
	type t = t_var
	let hash n = X.hash n.v + 257 * (uid n.p) + 65537 * (uid n.n)
	let equal n1 n2 = X.equal n1.v n2.v && n1.p == n2.p && n1.p == n2.p
      end
    )

  let unique = Unique.create 1024

  let rec dump f ppf = function
    | Zero -> Format.fprintf ppf "."
    | One -> Format.fprintf ppf "*"
    | Var (v,One,Zero,_,_) ->
	Format.fprintf ppf "%a" f v
    | Var (v,Zero,One,_,_) ->
	Format.fprintf ppf "~%a" f v
    | Var (v,One,n,_,_) ->
	Format.fprintf ppf "%a|%a" f v (dump f) n
    | Var (v,Zero,n,_,_) ->
	Format.fprintf ppf "~%a&%a" f v (dump f) n
    | Var (v,p,One,_,_) ->
	Format.fprintf ppf "~%a|%a" f v (dump f) p
    | Var (v,p,Zero,_,_) ->
	Format.fprintf ppf "%a&%a" f v (dump f) p
    | Var (v,p,n,_,uid) -> 
	Format.fprintf ppf "%a(%a,%a)"  f v (dump f) p (dump f) n


  let dmp = dump (fun ppf x -> Format.fprintf ppf "#%i" (X.hash x))

  let inject : t_var -> t = Obj.magic

  let cur_uid = ref 2
    
  let inv = function
    | Zero -> One
    | One -> Zero
    | Var (_,_,_,n,_) -> n

  let make var pos neg =
    if pos == neg then pos
    else (
      let n = { v=var; p=pos; n=neg; inv=Zero; uid=0 } in
      let n' = Unique.merge unique n in
      if n == n' then (
	n.uid <- !cur_uid; 
	incr cur_uid;
	let ninv = { v=var; p=inv pos; n=inv neg; 
		     inv=inject n; uid = !cur_uid } in
	n.inv <- inject ninv;
	incr cur_uid;
	Unique.add unique ninv;
      );
      inject n'
    )

  let and_cache_len = 10000
  let and_cache_res = Weak.create and_cache_len
  let and_cache_arg1 = Array.create and_cache_len (-1)
  let and_cache_arg2 = Array.create and_cache_len (-1)
    
  let rec (&&&) nod1 nod2 =
    if nod1 == nod2 then nod1
    else match nod1,nod2 with
      | Zero,_ | _,Zero -> Zero
      | One,nod | nod,One -> nod
      | Var (v1,p1,n1,inv1,id1), Var (v2,p2,n2,_,id2) ->
	  if inv1 == nod2 then Zero
	  else let h = ((id1 * 257 + id2) land max_int) mod and_cache_len in
	  let r =
	    if (and_cache_arg1.(h) == id1) && (and_cache_arg2.(h) == id2)
	    then Weak.get and_cache_res h 
	    else None
	  in match r with
	    | Some res -> res
	    | None -> 
		let c = X.compare v1 v2 in
		let res = 
		  if c = 0 then make v1 (p1 &&& p2) (n1 &&& n2)
		  else if c < 0 then make v1 (p1 &&& nod2) (n1 &&& nod2)
		  else make v2 (p2 &&& nod1) (n2 &&& nod1)
		in
(*		Format.fprintf Format.std_formatter
		  "(&&&) x=%a y=%a ==> %a@."
		  dmp nod1 dmp nod2 dmp res; *)
		and_cache_arg1.(h) <- id1; and_cache_arg2.(h) <- id2;
		Weak.set and_cache_res h (Some res);
		res
		

  let (|||) nod1 nod2 = inv ((inv nod1) &&& (inv nod2))
  let (---) nod1 nod2 = nod1 &&& (inv nod2)
  let (!!!) v = make v One Zero
  let (~~~) = inv

  let simpl_cache_len = 10000
  let simpl_cache_res = Weak.create simpl_cache_len
  let simpl_cache_arg1 = Array.create simpl_cache_len (-1)
  let simpl_cache_arg2 = Array.create simpl_cache_len (-1)
    
  let rec simpl nod1 nod2 =
    if nod1 == nod2 then nod1
    else match nod1,nod2 with
      | Zero,_ | _,Zero -> Zero
      | One,_ | _,One -> nod1
      | Var (v1,p1,n1,inv1,id1), Var (v2,p2,n2,_,id2) ->
	  if inv1 == nod2 then Zero
	  else let h = ((id1 * 257 + id2) land max_int) mod simpl_cache_len in
	  let r =
	    if (simpl_cache_arg1.(h) == id1) && (simpl_cache_arg2.(h) == id2)
	    then Weak.get simpl_cache_res h 
	    else None
	  in match r with
	    | Some res -> res
	    | None ->
		let c = X.compare v1 v2 in
		let res = 
		  if c = 0 then 
		    if p2 == Zero then simpl n1 n2
		    else if n2 == Zero then simpl p1 p2
		    else 
		      make v1 (simpl p1 p2) (simpl n1 n2)
		  else
		    if c < 0 then
		      make v1 (simpl p1 nod2) (simpl n1 nod2)
		    else
		      let u = p2 ||| n2 in
		      simpl nod1 u
		in
		simpl_cache_arg1.(h) <- id1; simpl_cache_arg2.(h) <- id2;
		Weak.set simpl_cache_res h (Some res);
(*		Format.fprintf Format.std_formatter "Simplif %a ; %a ==> %a@."
		  dmp nod1 dmp nod2 dmp res; *)
		res

(*
  let simpl nod1 nod2 =
    let res = simpl nod1 nod2 in
    let check1 = (nod1 ||| (~~~ nod2)) in
    let check2 = (res ||| (~~~ nod2)) in
    assert (check1 == check2);
(*      Format.fprintf Format.std_formatter "Simplif %a ; %a ==> %a@."
	dmp nod1 dmp nod2 dmp (simpl nod1 nod2); *)
    res
*)

  let one = One
  let zero = Zero

  let equal = (==)
  let hash n = uid n
  let compare n1 n2 = Pervasives.compare (uid n1) (uid n2)

  let dnf pos0 neg0 n =
    let rec aux accu pos neg = function
      | Zero -> accu
      | One -> (pos,neg)::accu
      | Var (x,p,Zero,_,_) -> aux accu (x::pos) neg p
      | Var (x,Zero,n,_,_) -> aux accu pos (x::neg) n
      | Var (x,One,n,_,_) -> aux ((x::pos,neg)::accu) pos neg n
      | Var (x,p,One,_,_) -> aux ((pos,x::neg)::accu) pos neg p 
      | Var (x,p,n,_,_) ->
	  if List.mem x pos0 then aux accu pos neg p
	  else if List.mem x neg0 then aux accu pos neg n
	  else
(*	  Format.fprintf Format.std_formatter
	    "p=%a n=%a  p---n=%a n---p=%a@." dmp p dmp n dmp (p ---n) dmp (n---p); *)
	  if (p --- n == Zero)
	  then aux (aux accu pos neg p) pos (x::neg) (simpl n (~~~ p))
	  else if (n --- p == Zero)
	  then aux (aux accu pos neg n) (x::pos) neg (simpl p (~~~ n))
	  else aux (aux accu (x::pos) neg p) pos (x::neg) n
    in
    aux [] pos0 neg0 n


  let dnf_enum cons ~pos ~neg =
    let rec aux accu cur = function
      | Zero -> accu
      | One -> cons cur accu
      | Var (x,p,Zero,_,_) -> aux accu (pos x cur) p
      | Var (x,Zero,n,_,_) -> aux accu (neg x cur) n
      | Var (x,One,n,_,_) -> aux (cons (pos x cur) accu) cur n
      | Var (x,p,One,_,_) -> aux (cons (neg x cur) accu) cur p 
      | Var (x,p,n,_,_) ->
	  if (p --- n == Zero)
	  then aux (aux accu cur p) (neg x cur) (simpl n (~~~ p))
	  else if (n --- p == Zero)
	  then aux (aux accu cur n) (pos x cur) (simpl p (~~~ n))
	  else aux (aux accu (pos x cur) p) (neg x cur) n
    in
    aux

  module VarSet = Set.Make(X)

(*
  let all_vars n = 
    let h = Hashtbl.create 20 in
    let all = ref VarSet.empty in
    let rec aux = function
      | Zero | One -> ()
      | Var (v,p,n,_,uid) ->
	  if Hashtbl.mem h uid then ()
	  else (Hashtbl.add h uid ();
		all := VarSet.add v !all;
		aux p; aux n)
    in
    aux n;
    !all
*)

  let factorize n =
    let h = Hashtbl.create 20 in
    let rec aux = function
      | Zero | One -> VarSet.empty,VarSet.empty
      | Var (v,p,n,_,uid) ->
	  try Hashtbl.find h uid
	  with Not_found ->
	    let r = 
	      if n == Zero then
		let pos_p,neg_p = aux p in
		VarSet.add v pos_p, neg_p
	      else if p == Zero then
		let pos_n,neg_n = aux n in
		pos_n, VarSet.add v neg_n
	      else
		let pos_p,neg_p = aux p
		and pos_n,neg_n = aux n in
		VarSet.inter pos_p pos_n, VarSet.inter neg_p neg_n in
	    Hashtbl.add h uid r;
	    r
    in
    aux n

  let dnf n =
    let pos,neg = VarSet.empty, VarSet.empty (* factorize n *) in
(*    Printf.eprintf "%i,%i\n" (List.length (VarSet.elements pos))
      (List.length (VarSet.elements neg)); *)
    dnf (VarSet.elements pos) (VarSet.elements neg) n

end

(*
module M = Make(
  struct 
    type t = int
    let compare = compare
    let equal = (==)
    let hash x = x
  end
)


let dmp = M.dump (fun ppf x -> Format.fprintf ppf "%i" x)

let rec print_list f sep ppf = function
  | [] -> ()
  | [hd] -> f ppf hd
  | hd::tl -> f ppf hd; Format.fprintf ppf "%s" sep; print_list f sep ppf tl

let dmp_dnf ppf l =
  print_list
    (fun ppf (pos,neg) ->
       Format.fprintf ppf "(%a;%a)"
	 (print_list (fun ppf x -> Format.fprintf ppf "%i" x) ",") pos
	 (print_list (fun ppf x -> Format.fprintf ppf "%i" x) ",") neg
    )
    "|"
    ppf l

open M

let () =
  let a = !!! 4 and b = !!! 2 and c = !!! 3 and d = !!! 6
					    and e = !!! 10 and f = !!! 11 in 
(*  let a = !!! 1 and b = !!! 2 and c = !!! 3 and d = !!! 4
					    and e = !!! 5 and f = !!! 6 in  *)
  let x = ((a &&& b) ||| (c &&& d) ||| (e &&& f)) ||| (!!!8 &&& !!!13 &&& !!!0) in
  Format.fprintf Format.std_formatter "X=%a@.DNF=%a@." 
    dmp x dmp_dnf (dnf x)
*)
