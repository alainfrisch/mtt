type atom = int

module AtomSet = struct
  type t = Finite of Pt.Set.t | Cofinite of Pt.Set.t

  let print ppf = function
    | Finite s ->
 	Format.fprintf ppf "%s"
	  (String.concat "|" (List.map string_of_int (Pt.Set.elements s)))
    | Cofinite s ->
 	Format.fprintf ppf "~(%s)"
	  (String.concat "|" (List.map string_of_int (Pt.Set.elements s)))

  let is_in i = function
    | Finite s -> Pt.Set.mem i s
    | Cofinite s -> not (Pt.Set.mem i s)

  let singleton s = Finite (Pt.Set.singleton s)

  let neg  = function
    | Finite s -> Cofinite s
    | Cofinite s -> Finite s

  let is_empty = function
    | Finite s -> Pt.Set.is_empty s
    | Cofinite _ -> false

  let is_any = function
    | Cofinite s -> Pt.Set.is_empty s
    | Finite _ -> false

  let inter s1 s2 = match s1,s2 with
    | Finite s1, Finite s2 -> Finite (Pt.Set.inter s1 s2)
    | Cofinite s1, Cofinite s2 -> Cofinite (Pt.Set.union s1 s2)
    | Finite s1, Cofinite s2
    | Cofinite s2, Finite s1 -> Finite (Pt.Set.diff s1 s2)

  let diff s1 s2 = match s1,s2 with
    | Finite s1, Cofinite s2 -> Finite (Pt.Set.inter s1 s2)
    | Cofinite s1, Finite s2 -> Cofinite (Pt.Set.union s1 s2)
    | Finite s1, Finite s2
    | Cofinite s2, Cofinite s1 -> Finite (Pt.Set.diff s1 s2)

  let union s1 s2 = match s1,s2 with
    | Finite s1, Finite s2 -> Finite (Pt.Set.union s1 s2)
    | Cofinite s1, Cofinite s2 -> Cofinite (Pt.Set.inter s1 s2)
    | Finite s1, Cofinite s2
    | Cofinite s2, Finite s1 -> Cofinite (Pt.Set.diff s2 s1)

  let any = Cofinite Pt.Set.empty
  let empty = Finite Pt.Set.empty

  let equal s1 s2 = s1 = s2
(* match s1,s2 with
    | Finite s1, Finite s2
    | Cofinite s1, Cofinite s2 -> Pt.Set.equal s1 s2
    | _ -> false *)

  let hash s = Hashtbl.hash s

  let compare s1 s2 = Pervasives.compare s1 s2
end

type 'a fstsnd = Fst of 'a | Snd of 'a
type 'a node = {
  uid: int;
  mutable atoms: AtomSet.t;
  mutable trans: 'a
}

module rec Node :  Robdd.HashedOrdered with type t = Trans.t node =
struct
  type t = Trans.t node
  let equal n1 n2 = 
    (n1 == n2) ||
      ((Trans.equal n1.trans n2.trans) && (AtomSet.equal n1.atoms n2.atoms))
  let hash n =
    Trans.hash n.trans + 65537 * (AtomSet.hash n.atoms)
  let compare n1 n2 =
    let c = Trans.compare n1.trans n2.trans in
    if c != 0 then c else AtomSet.compare n1.atoms n2.atoms
end 
and Trans : Robdd.S with type var = FstSnd.t = Robdd.Make(FstSnd)
and FstSnd : Robdd.HashedOrdered with type t = Node.t fstsnd = 
struct
  type t = Node.t fstsnd
  let equal x y = match x,y with
    | Fst n1, Fst n2 | Snd n1, Snd n2 -> n1 == n2
    | _ -> false
  let hash = function
    | Fst n -> 2 * n.uid
    | Snd n -> 2 * n.uid + 1
  let compare x y = match x,y with
    | Fst n1, Fst n2 -> n2.uid - n1.uid
    | Snd n1, Snd n2 -> n2.uid - n1.uid
    | Fst _, Snd _ -> (-1)
    | Snd _, Fst _ -> 1
(*  let compare x y = match x,y with
    | (Fst n1 | Snd n1), (Fst n2 | Snd n2) ->
	if n1 == n2 then match x,y with
	  | Fst _, Fst _ | Snd _, Snd _ -> 0
	  | Fst _, Snd _ -> 1 | _ -> -1
	else n2.uid - n1.uid *)
end

include Node

let cur_id = ref 0

let typ atoms tr = incr cur_id; { uid = !cur_id; atoms = atoms; trans = tr }

let any = typ AtomSet.any Trans.one
let empty = typ AtomSet.empty Trans.zero
let any_pair = typ AtomSet.empty Trans.one
let any_atom = typ AtomSet.any Trans.zero

type delayed = t

let mk () = typ AtomSet.any Trans.one
let def n t = n.atoms <- t.atoms; n.trans <- t.trans
let get_delayed t = t

let inter t1 t2 = 
  typ (AtomSet.inter t1.atoms t2.atoms) (Trans.(&&&) t1.trans t2.trans)
let diff t1 t2 = 
  typ (AtomSet.diff t1.atoms t2.atoms) (Trans.(---) t1.trans t2.trans)
let union t1 t2 = 
  typ (AtomSet.union t1.atoms t2.atoms) (Trans.(|||) t1.trans t2.trans)
let neg t =
  typ (AtomSet.neg t.atoms) (Trans.(~~~) t.trans)

let dnf_trans =
  Trans.dnf_enum
    (fun x accu -> x :: accu)
    ~pos:(fun x (fst,snd) -> match x with
	    | Fst t -> inter t fst, snd
	    | Snd t -> fst, inter t snd)
    ~neg:(fun x (fst,snd) -> match x with
	    | Fst t -> diff fst t, snd
	    | Snd t -> fst, diff snd t)
    [] (any,any)


module TransHash = Hashtbl.Make(Trans)

let empty_memo = TransHash.create 4096
let empty_stack = ref []

let rec unstack tr = function
  | hd::tl when hd == tr -> tl
  | hd::tl -> TransHash.remove empty_memo hd; unstack tr tl
  | [] -> assert false

let rec is_empty t =
  (AtomSet.is_empty t.atoms) && (
    let tr = t.trans in
    try TransHash.find empty_memo tr
    with Not_found ->
      TransHash.add empty_memo tr true;
      empty_stack := tr :: !empty_stack;
      if 
	List.for_all 
	  (fun (fst,snd) -> is_empty fst || is_empty snd) 
	  (dnf_trans tr)
      then true
      else (
	TransHash.replace empty_memo tr false;
	empty_stack := unstack tr !empty_stack;
	false
      )
  )

let is_empty t =
  let r = is_empty t in
  empty_stack := [];
  r

let subset t1 t2 = is_empty (diff t1 t2)
let disjoint t1 t2 = is_empty (inter t1 t2)

let fst t = typ AtomSet.empty (Trans.(!!!) (Fst t))
let snd t = typ AtomSet.empty (Trans.(!!!) (Snd t))
let atom i = typ (AtomSet.singleton i) Trans.zero

let dnf_pair t = dnf_trans t.trans

let dnf_neg_pair t = dnf_trans (Trans.(~~~) t.trans)

type v = Atom of atom | Pair of v * v

let rec is_in v t = match v with
  | Atom i -> AtomSet.is_in i t.atoms
  | Pair (v1,v2) -> 
      List.exists 
	(fun (t1,t2) -> is_in v1 t1 && is_in v2 t2) 
	(dnf_pair t)  (* todo: don't build the dnf here *)

let is_trivially_empty t = Trans.is_zero t.trans && AtomSet.is_empty t.atoms
let is_trivially_any t = Trans.is_one t.trans && AtomSet.is_any t.atoms

let dump_tr l ppf = function
  | Fst x -> l := x::!l; Format.fprintf ppf "L%i" x.uid
  | Snd x -> l := x::!l; Format.fprintf ppf "R%i" x.uid

let print ppf t =
  let l = ref [t] in
  let p = ref [] in
  let rec loop () =
    match !l with
      | [] -> ()
      | t::rest ->
	  l := rest;
	  if List.memq t !p then ()
	  else (
	    p := t :: !p;
	    Format.fprintf ppf "%i:={atoms:%a;pairs:%a==%a}@\n" t.uid
	      AtomSet.print t.atoms
	      (Trans.dump_dnf (dump_tr l)) t.trans
	      (Trans.dump (dump_tr l)) t.trans
	  );
	  loop ()
  in
  loop ()

