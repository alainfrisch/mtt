type 'a re =
  | Eps
  | Elem of 'a
  | Seq of 'a re * 'a re
  | Alt of 'a re * 'a re
  | Star of 'a re
  | Plus of 'a re
  | Any

module type S = sig
  type t
  type node
  val union: t -> t -> t
  val eps: t
  val empty: t
  val any: t

  val snd: node -> t
  val mk: unit -> node
  val def: node -> t -> unit

  type elt
  val equal: elt -> elt -> bool
  val hash: elt -> int

  val elt: elt -> node -> t
end

module Compile(X : S) : 
sig val compile : X.elt re -> X.t end = struct


let rec equal_re re1 re2 = match re1,re2 with
  | Eps,Eps | Any,Any -> true
  | Elem e1, Elem e2 -> e1 == e2
  | Seq (r1,r2), Seq (r1',r2') 
  | Alt (r1,r2), Alt (r1',r2') -> equal_re r1 r1' && equal_re r2 r2'
  | Star r, Star r' | Plus r, Plus r' -> equal_re r r'
  | _ -> false

let rec hash_re = function
  | Eps -> 0
  | Elem e -> 1 + 17 * (X.hash e)
  | Seq (r1,r2) -> 2 + 17 * (hash_re r1) + 257 * (hash_re r2)
  | Alt (r1,r2) -> 3 + 17 * (hash_re r1) + 257 * (hash_re r2)
  | Star r -> 4 + 17 * (hash_re r)
  | Plus r -> 5 + 17 * (hash_re r)
  | Any -> 6

let rec equal_rl rl1 rl2 = match rl1,rl2 with
  | [],[] -> true
  | r1::rl1, r2::rl2 -> equal_re r1 r2 && equal_rl rl1 rl2
  | _ -> false

let rec hash_rl = function
  | [] -> 1
  | hd::tl -> 2 + 17 * (hash_re hd) + 65537 * (hash_rl tl)

module H = Hashtbl.Make(struct
			  type t = X.elt re list
			  let equal = equal_rl
			  let hash = hash_rl
			end)

let nodes = H.create 1024

let rec nod_of l =
  try H.find nodes l
  with Not_found -> 
    let n = X.mk () in
    H.add nodes l n;
    X.def n (compile l);
    n

and compile l =
  let seen = H.create 16 in
  let tr = ref X.empty in
  let rec aux l =
    if H.mem seen l then ()
    else (H.add seen l ();
	  match l with
	    | [] -> tr := X.union !tr X.eps
	    | [Any] -> tr := X.any
	    | Any :: rest -> aux rest; tr := X.union !tr (X.snd (nod_of l))
	    | Eps :: rest -> aux rest
	    | Elem x :: rest -> tr := X.union !tr (X.elt x (nod_of rest))
	    | Seq (r1,r2) :: rest -> aux (r1 :: r2 :: rest)
	    | Alt (r1,r2) :: rest -> aux (r1 :: rest); aux (r2 :: rest)
	    | Star r :: rest -> aux (r :: l); aux rest
	    | Plus r :: rest -> aux (r :: Star r :: rest))
  in
  aux l;
  !tr

let compile re = compile [re]

end
