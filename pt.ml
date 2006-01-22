(* Sets and maps over integer implemented as Patricia trees.
   Code borrowed from J.C. Filliatre. *)

module Set = struct
(*i*)
type elt = int
(*i*)

type t =
  | Empty
  | Leaf of int
  | Branch of int * int * t * t

(*s Example: the representation of the set $\{1,4,5\}$ is
    $$\mathtt{Branch~(0,~1,~Leaf~4,~Branch~(1,~4,~Leaf~1,~Leaf~5))}$$
    The first branching bit is the bit 0 (and the corresponding prefix
    is [0b0], not of use here), with $\{4\}$ on the left and $\{1,5\}$ on the
    right. Then the right subtree branches on bit 2 (and so has a branching 
    value of $2^2 = 4$), with prefix [0b01 = 1]. *)

(*s Empty set and singletons. *)

let empty = Empty

let is_empty = function Empty -> true | _ -> false

let singleton k = Leaf k

(*s Testing the occurrence of a value is similar to the search in a
    binary search tree, where the branching bit is used to select the
    appropriate subtree. *)

let zero_bit k m = (k land m) == 0

let rec mem k = function
  | Empty -> false
  | Leaf j -> k == j
  | Branch (_, m, l, r) -> mem k (if zero_bit k m then l else r)

(*s The following operation [join] will be used in both insertion and
    union. Given two non-empty trees [t0] and [t1] with longest common
    prefixes [p0] and [p1] respectively, which are supposed to
    disagree, it creates the union of [t0] and [t1]. For this, it
    computes the first bit [m] where [p0] and [p1] disagree and create
    a branching node on that bit. Depending on the value of that bit
    in [p0], [t0] will be the left subtree and [t1] the right one, or
    the converse. Computing the first branching bit of [p0] and [p1]
    uses a nice property of twos-complement representation of integers. *)

let lowest_bit x = x land (-x)

let branching_bit p0 p1 = lowest_bit (p0 lxor p1)

let mask p m = p land (m-1)

let join (p0,t0,p1,t1) =
  let m = branching_bit p0 p1 in
  if zero_bit p0 m then 
    Branch (mask p0 m, m, t0, t1)
  else 
    Branch (mask p0 m, m, t1, t0)

(*s Then the insertion of value [k] in set [t] is easily implemented
    using [join].  Insertion in a singleton is just the identity or a
    call to [join], depending on the value of [k].  When inserting in
    a branching tree, we first check if the value to insert [k]
    matches the prefix [p]: if not, [join] will take care of creating
    the above branching; if so, we just insert [k] in the appropriate
    subtree, depending of the branching bit. *)

let match_prefix k p m = (mask k m) == p

let add k t =
  let rec ins = function
    | Empty -> Leaf k
    | Leaf j as t -> 
	if j == k then t else join (k, Leaf k, j, t)
    | Branch (p,m,t0,t1) as t ->
	if match_prefix k p m then
	  if zero_bit k m then 
	    Branch (p, m, ins t0, t1)
	  else
	    Branch (p, m, t0, ins t1)
	else
	  join (k, Leaf k, p, t)
  in
  ins t

(*s The code to remove an element is basically similar to the code of
    insertion. But since we have to maintain the invariant that both
    subtrees of a [Branch] node are non-empty, we use here the 
    ``smart constructor'' [branch] instead of [Branch]. *)

let branch = function
  | (_,_,Empty,t) -> t
  | (_,_,t,Empty) -> t
  | (p,m,t0,t1)   -> Branch (p,m,t0,t1)

let remove k t =
  let rec rmv = function
    | Empty -> Empty
    | Leaf j as t -> if k == j then Empty else t
    | Branch (p,m,t0,t1) as t -> 
	if match_prefix k p m then
	  if zero_bit k m then
	    branch (p, m, rmv t0, t1)
	  else
	    branch (p, m, t0, rmv t1)
	else
	  t
  in
  rmv t

(*s One nice property of Patricia trees is to support a fast union
    operation (and also fast subset, difference and intersection
    operations). When merging two branching trees we examine the
    following four cases: (1) the trees have exactly the same
    prefix; (2/3) one prefix contains the other one; and (4) the
    prefixes disagree. In cases (1), (2) and (3) the recursion is
    immediate; in case (4) the function [join] creates the appropriate
    branching. *)

let rec merge = function
  | Empty, t  -> t
  | t, Empty  -> t
  | Leaf k, t -> add k t
  | t, Leaf k -> add k t
  | (Branch (p,m,s0,s1) as s), (Branch (q,n,t0,t1) as t) ->
      if m == n && match_prefix q p m then
	(* The trees have the same prefix. Merge the subtrees. *)
	Branch (p, m, merge (s0,t0), merge (s1,t1))
      else if m < n && match_prefix q p m then
	(* [q] contains [p]. Merge [t] with a subtree of [s]. *)
	if zero_bit q m then 
	  Branch (p, m, merge (s0,t), s1)
        else 
	  Branch (p, m, s0, merge (s1,t))
      else if m > n && match_prefix p q n then
	(* [p] contains [q]. Merge [s] with a subtree of [t]. *)
	if zero_bit p n then
	  Branch (q, n, merge (s,t0), t1)
	else
	  Branch (q, n, t0, merge (s,t1))
      else
	(* The prefixes disagree. *)
	join (p, s, q, t)

let union s t = merge (s,t)

(*s When checking if [s1] is a subset of [s2] only two of the above
    four cases are relevant: when the prefixes are the same and when the
    prefix of [s1] contains the one of [s2], and then the recursion is
    obvious. In the other two cases, the result is [false]. *)

let rec subset s1 s2 = match (s1,s2) with
  | Empty, _ -> true
  | _, Empty -> false
  | Leaf k1, _ -> mem k1 s2
  | Branch _, Leaf _ -> false
  | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
	subset l1 l2 && subset r1 r2
      else if m1 > m2 && match_prefix p1 p2 m2 then
	if zero_bit p1 m2 then 
	  subset l1 l2 && subset r1 l2
	else 
	  subset l1 r2 && subset r1 r2
      else
	false

(*s To compute the intersection and the difference of two sets, we
    still examine the same four cases as in [merge]. The recursion is
    then obvious. *)

let rec inter s1 s2 = match (s1,s2) with
  | Empty, _ -> Empty
  | _, Empty -> Empty
  | Leaf k1, _ -> if mem k1 s2 then s1 else Empty
  | _, Leaf k2 -> if mem k2 s1 then s2 else Empty
  | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then 
	merge (inter l1 l2, inter r1 r2)
      else if m1 < m2 && match_prefix p2 p1 m1 then
	inter (if zero_bit p2 m1 then l1 else r1) s2
      else if m1 > m2 && match_prefix p1 p2 m2 then
	inter s1 (if zero_bit p1 m2 then l2 else r2)
      else
	Empty

let rec diff s1 s2 = match (s1,s2) with
  | Empty, _ -> Empty
  | _, Empty -> s1
  | Leaf k1, _ -> if mem k1 s2 then Empty else s1
  | _, Leaf k2 -> remove k2 s1
  | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
	merge (diff l1 l2, diff r1 r2)
      else if m1 < m2 && match_prefix p2 p1 m1 then
	if zero_bit p2 m1 then 
	  merge (diff l1 s2, r1) 
	else 
	  merge (l1, diff r1 s2)
      else if m1 > m2 && match_prefix p1 p2 m2 then
	if zero_bit p1 m2 then diff s1 l2 else diff s1 r2
      else
	s1

(*s All the following operations ([cardinal], [iter], [fold], [for_all],
    [exists], [filter], [partition], [choose], [elements]) are
    implemented as for any other kind of binary trees. *)

let rec cardinal = function
  | Empty -> 0
  | Leaf _ -> 1
  | Branch (_,_,t0,t1) -> cardinal t0 + cardinal t1

let rec iter f = function
  | Empty -> ()
  | Leaf k -> f k
  | Branch (_,_,t0,t1) -> iter f t0; iter f t1
      
let rec fold f s accu = match s with
  | Empty -> accu
  | Leaf k -> f k accu
  | Branch (_,_,t0,t1) -> fold f t0 (fold f t1 accu)

let rec for_all p = function
  | Empty -> true
  | Leaf k -> p k
  | Branch (_,_,t0,t1) -> for_all p t0 && for_all p t1

let rec exists p = function
  | Empty -> false
  | Leaf k -> p k
  | Branch (_,_,t0,t1) -> exists p t0 || exists p t1

let filter p s = 
  let rec filt acc = function
    | Empty -> acc
    | Leaf k -> if p k then add k acc else acc
    | Branch (_,_,t0,t1) -> filt (filt acc t0) t1
  in
  filt Empty s

let partition p s =
  let rec part (t,f as acc) = function
    | Empty -> acc
    | Leaf k -> if p k then (add k t, f) else (t, add k f)
    | Branch (_,_,t0,t1) -> part (part acc t0) t1
  in
  part (Empty, Empty) s

let rec choose = function
  | Empty -> raise Not_found
  | Leaf k -> k
  | Branch (_, _,t0,_) -> choose t0   (* we know that [t0] is non-empty *)

let elements s =
  let rec elements_aux acc = function
    | Empty -> acc
    | Leaf k -> k :: acc
    | Branch (_,_,l,r) -> elements_aux (elements_aux acc l) r
  in
  elements_aux [] s

let split x s =
  let coll k (l, b, r) =
    if k < x then add k l, b, r
    else if k > x then l, b, add k r
    else l, true, r 
  in
  fold coll s (Empty, false, Empty)

(*s There is no way to give an efficient implementation of [min_elt]
    and [max_elt], as with binary search trees.  The following
    implementation is a traversal of all elements, barely more
    efficient than [fold min t (choose t)] (resp. [fold max t (choose
    t)]). Note that we use the fact that there is no constructor
    [Empty] under [Branch] and therefore always a minimal
    (resp. maximal) element there. *)

let rec min_elt = function
  | Empty -> raise Not_found
  | Leaf k -> k
  | Branch (_,_,s,t) -> min (min_elt s) (min_elt t)

let rec max_elt = function
  | Empty -> raise Not_found
  | Leaf k -> k
  | Branch (_,_,s,t) -> max (max_elt s) (max_elt t)

(*s Another nice property of Patricia trees is to be independent of the
    order of insertion. As a consequence, two Patricia trees have the
    same elements if and only if they are structurally equal. *)

let equal t1 t2 =
  let rec equal_aux t1 t2 = match t1, t2 with
    | Empty, Empty -> true
    | Leaf x1, Leaf x2 -> x1 = x2
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
	p1 = p2 && m1 = m2 && equal_aux l1 l2 && equal_aux r1 r2
    | _ -> false
  in
  equal_aux t1 t2


let compare = compare

(*i*)
let make l = List.fold_right add l empty
(*i*)

(*s Additional functions w.r.t to [Set.S]. *)

let rec intersect s1 s2 = match (s1,s2) with
  | Empty, _ -> false
  | _, Empty -> false
  | Leaf k1, _ -> mem k1 s2
  | _, Leaf k2 -> mem k2 s1
  | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
        intersect l1 l2 || intersect r1 r2
      else if m1 < m2 && match_prefix p2 p1 m1 then
        intersect (if zero_bit p2 m1 then l1 else r1) s2
      else if m1 > m2 && match_prefix p1 p2 m2 then
        intersect s1 (if zero_bit p1 m2 then l2 else r2)
      else
        false

let rec hash = function
  | Empty -> 0
  | Leaf k -> 17 * k
  | Branch (p,m,l,r) ->  p + 17 * m + 257 * (hash l) + 65537 * (hash r)
end

module Map = struct
(*
 * Ptmap: Maps over integers implemented as Patricia trees.
 * Copyright (C) 2000 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file LGPL).
 *)

(*i $Id$ i*)

(*s Maps of integers implemented as Patricia trees, following Chris
    Okasaki and Andrew Gill's paper {\em Fast Mergeable Integer Maps}
    ({\tt\small http://www.cs.columbia.edu/\~{}cdo/papers.html\#ml98maps}).
    See the documentation of module [Ptset] which is also based on the
    same data-structure. *)

type key = int

type 'a t =
  | Empty
  | Leaf of int * 'a
  | Branch of int * int * 'a t * 'a t

let empty = Empty

let is_empty t = t = Empty

let singleton k x = Leaf (k,x)

let zero_bit k m = (k land m) == 0

let rec mem k = function
  | Empty -> false
  | Leaf (j,_) -> k == j
  | Branch (_, m, l, r) -> mem k (if zero_bit k m then l else r)

let rec find k = function
  | Empty -> raise Not_found
  | Leaf (j,x) -> if k == j then x else raise Not_found
  | Branch (_, m, l, r) -> find k (if zero_bit k m then l else r)

let lowest_bit x = x land (-x)

let branching_bit p0 p1 = lowest_bit (p0 lxor p1)

let mask p m = p land (m-1)

let join (p0,t0,p1,t1) =
  let m = branching_bit p0 p1 in
  if zero_bit p0 m then 
    Branch (mask p0 m, m, t0, t1)
  else 
    Branch (mask p0 m, m, t1, t0)

let match_prefix k p m = (mask k m) == p

let add k x t =
  let rec ins = function
    | Empty -> Leaf (k,x)
    | Leaf (j,_) as t -> 
	if j == k then Leaf (k,x) else join (k, Leaf (k,x), j, t)
    | Branch (p,m,t0,t1) as t ->
	if match_prefix k p m then
	  if zero_bit k m then 
	    Branch (p, m, ins t0, t1)
	  else
	    Branch (p, m, t0, ins t1)
	else
	  join (k, Leaf (k,x), p, t)
  in
  ins t

let set k f t =
  let rec ins = function
    | Empty -> Leaf (k, f None)
    | Leaf (j,x) as t -> 
	if j == k then Leaf (k,f (Some x)) else join (k, Leaf (k,f None), j, t)
    | Branch (p,m,t0,t1) as t ->
	if match_prefix k p m then
	  if zero_bit k m then 
	    Branch (p, m, ins t0, t1)
	  else
	    Branch (p, m, t0, ins t1)
	else
	  join (k, Leaf (k,f None), p, t)
  in
  ins t

let branch = function
  | (_,_,Empty,t) -> t
  | (_,_,t,Empty) -> t
  | (p,m,t0,t1)   -> Branch (p,m,t0,t1)

let remove k t =
  let rec rmv = function
    | Empty -> Empty
    | Leaf (j,_) as t -> if k == j then Empty else t
    | Branch (p,m,t0,t1) as t -> 
	if match_prefix k p m then
	  if zero_bit k m then
	    branch (p, m, rmv t0, t1)
	  else
	    branch (p, m, t0, rmv t1)
	else
	  t
  in
  rmv t

let may_leaf k = function
  | None -> Empty
  | Some x -> Leaf (k,x)

let unset k f t =
  let rec ins = function
    | Empty -> Empty
    | Leaf (j,x) as t -> 
	if j == k then may_leaf k (f x) 
	else t
    | Branch (p,m,t0,t1) as t ->
	if match_prefix k p m then
	  if zero_bit k m then 
	    branch (p, m, ins t0, t1)
	  else
	    branch (p, m, t0, ins t1)
	else
	  t
  in
  ins t

let rec iter f = function
  | Empty -> ()
  | Leaf (k,x) -> f k x
  | Branch (_,_,t0,t1) -> iter f t0; iter f t1

let rec map f = function
  | Empty -> Empty
  | Leaf (k,x) -> Leaf (k, f x)
  | Branch (p,m,t0,t1) -> Branch (p, m, map f t0, map f t1)
      
let rec mapi f = function
  | Empty -> Empty
  | Leaf (k,x) -> Leaf (k, f k x)
  | Branch (p,m,t0,t1) -> Branch (p, m, mapi f t0, mapi f t1)
      
let rec fold f s accu = match s with
  | Empty -> accu
  | Leaf (k,x) -> f k x accu
  | Branch (_,_,t0,t1) -> fold f t0 (fold f t1 accu)

(* we order constructors as Empty < Leaf < Branch *)
let compare cmp t1 t2 =
  let rec compare_aux t1 t2 = match t1,t2 with
    | Empty, Empty -> 0
    | Empty, _ -> -1
    | _, Empty -> 1
    | Leaf (k1,x1), Leaf (k2,x2) ->
	let c = compare k1 k2 in 
	if c <> 0 then c else cmp x1 x2
    | Leaf _, Branch _ -> -1
    | Branch _, Leaf _ -> 1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
	let c = compare p1 p2 in
	if c <> 0 then c else
	let c = compare m1 m2 in
	if c <> 0 then c else
        let c = compare_aux l1 l2 in
        if c <> 0 then c else
        compare_aux r1 r2
  in
  compare_aux t1 t2

let equal eq t1 t2 =
  let rec equal_aux t1 t2 = match t1, t2 with
    | Empty, Empty -> true
    | Leaf (k1,x1), Leaf (k2,x2) -> k1 = k2 && eq x1 x2
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
	p1 = p2 && m1 = m2 && equal_aux l1 l2 && equal_aux r1 r2
    | _ -> false
  in
  equal_aux t1 t2

let rec hash h = function
  | Empty -> 0
  | Leaf (k,x) -> k + 17 * (h x)
  | Branch (p,m,l,r) ->  p + 17 * m + 257 * (hash h l) + 65537 * (hash h r)

let rec subset f s1 s2 = match (s1,s2) with
  | Empty, _ -> true
  | _, Empty -> false
  | Leaf (k1,x1), _ -> (try f x1 (find k1 s2) with Not_found -> false)
  | Branch _, Leaf _ -> false
  | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
        subset f l1 l2 && subset f r1 r2
      else if m1 > m2 && match_prefix p1 p2 m2 then
        if zero_bit p1 m2 then 
          subset f l1 l2 && subset f r1 l2
        else 
          subset f l1 r2 && subset f r1 r2
      else
        false

let rec disjoint f s1 s2 = match (s1,s2) with
  | Empty, _ | _, Empty -> true
  | Leaf (k,x), s 
  | s, Leaf (k,x) -> (try f x (find k s) with Not_found -> true)
  | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
        disjoint f l1 l2 && disjoint f r1 r2
      else if m1 > m2 && match_prefix p1 p2 m2 then
        if zero_bit p1 m2 then 
          disjoint f l1 l2 && disjoint f r1 l2
        else 
          disjoint f l1 r2 && disjoint f r1 r2
      else if m2 > m1 && match_prefix p2 p1 m1 then
        if zero_bit p2 m1 then 
          disjoint f l1 l2 && disjoint f l1 r2
        else 
          disjoint f r1 l2 && disjoint f r1 r2
      else true

let rec union f t1 t2 = match (t1,t2) with
  | Empty, t | t, Empty -> t
  | (Leaf (k,x) as t0), t | t, (Leaf (k,x) as t0) -> 
      let rec ins = function
	| Empty -> Leaf (k, x)
	| Leaf (j,y) as t -> 
	    if j == k then Leaf (k,f x y) else join (k, t0, j, t)
	| Branch (p,m,l,r) as t ->
	    if match_prefix k p m then
	      if zero_bit k m then 
		Branch (p, m, ins l, r)
	      else
		Branch (p, m, l, ins r)
	    else
	      join (k, t0, p, t) in
      ins t
  | (Branch (p,m,s0,s1) as s), (Branch (q,n,t0,t1) as t) ->
      if m == n && match_prefix q p m then
	Branch (p, m, union f s0 t0, union f s1 t1)
      else if m < n && match_prefix q p m then
	(* [q] contains [p]. Merge [t] with a subtree of [s]. *)
	if zero_bit q m then 
	  Branch (p, m, union f s0 t, s1)
        else 
	  Branch (p, m, s0, union f s1 t)
      else if m > n && match_prefix p q n then
	(* [p] contains [q]. Merge [s] with a subtree of [t]. *)
	if zero_bit p n then
	  Branch (q, n, union f s t0, t1)
	else
	  Branch (q, n, t0, union f s t1)
      else
	(* The prefixes disagree. *)
	join (p, s, q, t)

let is_singleton f = function
  | Leaf (k,x) -> f x
  | _ -> None

let rec diff f t1 t2 = match (t1,t2) with
  | t, Empty -> t
  | Empty, t -> Empty
  | Leaf (k,x), _ -> (try may_leaf k (f x (find k t2)) with Not_found -> t1)
  | _, Leaf (k,x) ->
      let rec ins = function
	| Empty -> Empty
	| Leaf (j,y) as t -> 
	    if j == k then may_leaf k (f y x) 
	    else t
	| Branch (p,m,t0,t1) as t ->
	    if match_prefix k p m then
	      if zero_bit k m then 
		branch (p, m, ins t0, t1)
	      else
		branch (p, m, t0, ins t1)
	    else
	      t
      in
      ins t1
  | (Branch (p,m,s0,s1) as s), (Branch (q,n,t0,t1) as t) ->
      if m == n && match_prefix q p m then
	branch (p,m,diff f s0 t0,diff f s1 t1)
      else if m < n && match_prefix q p m then
	(* [q] contains [p]. Merge [t] with a subtree of [s]. *)
	if zero_bit q m then 
	  branch (p,m,diff f s0 t,s1)
        else 
	  branch (p,m,s0,diff f s1 t)
      else if m > n && match_prefix p q n then
	(* [p] contains [q]. Merge [s] with a subtree of [t]. *)
	if zero_bit p n then
	  diff f s t0
	else 
	  diff f s t1
      else
	s


let rec restrict t1 t2 = match (t1,t2) with
  | t, Set.Empty -> t
  | Empty, _ -> Empty
  | Leaf (k,x), _ -> if Set.mem k t2 then Empty else t1
  | _, Set.Leaf k -> remove k t1
  | (Branch (p,m,s0,s1) as s), (Set.Branch (q,n,t0,t1) as t) ->
      if m == n && match_prefix q p m then
	branch (p,m,restrict s0 t0,restrict s1 t1)
      else if m < n && match_prefix q p m then
	(* [q] contains [p]. Merge [t] with a subtree of [s]. *)
	if zero_bit q m then 
	  branch (p,m,restrict s0 t,s1)
        else 
	  branch (p,m,s0,restrict s1 t)
      else if m > n && match_prefix p q n then
	(* [p] contains [q]. Merge [s] with a subtree of [t]. *)
	if zero_bit p n then
	  restrict s t0
	else 
	  restrict s t1
      else
	s


end
