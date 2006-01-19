type atom = int

module AtomSet = struct
  type t = Finite of Ptset.t | Cofinite of Ptset.t

  let singleton s = Finite (Ptset.singleton s)

  let is_empty = function
    | Finite s -> Ptset.is_empty s
    | Cofinite _ -> false

  let inter s1 s2 = match s1,s2 with
    | Finite s1, Finite s2 -> Finite (Ptset.inter s1 s2)
    | Cofinite s1, Cofinite s2 -> Cofinite (Ptset.union s1 s2)
    | Finite s1, Cofinite s2
    | Cofinite s2, Finite s1 -> Finite (Ptset.diff s1 s2)

  let diff s1 s2 = match s1,s2 with
    | Finite s1, Cofinite s2 -> Finite (Ptset.inter s1 s2)
    | Cofinite s1, Finite s2 -> Cofinite (Ptset.union s1 s2)
    | Finite s1, Finite s2
    | Cofinite s2, Cofinite s1 -> Finite (Ptset.diff s1 s2)

  let any = Cofinite Ptset.empty
  let empty = Finite Ptset.empty

  let equal s1 s2 = s1 = s2
(* match s1,s2 with
    | Finite s1, Finite s2
    | Cofinite s1, Cofinite s2 -> Ptset.equal s1 s2
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
    | Fst n1, Fst n2 -> n1.uid - n2.uid
    | Snd n1, Snd n2 -> n1.uid - n2.uid
    | Fst _, Snd _ -> (-1)
    | Snd _, Fst _ -> (-1)
end

let cur_id = ref 0

let cons atoms tr =
  incr cur_id;
  { uid = !cur_id;
    atoms = atoms;
    trans = tr }

let any = cons AtomSet.any Trans.one

let mk () = cons any.atoms any.trans
let def n t = n.atoms <- t.atoms; n.trans <- t.trans

let inter t1 t2 = 
  cons (AtomSet.inter t1.atoms t2.atoms) (Trans.(&&&) t1.trans t2.trans)
let diff t1 t2 = 
  cons (AtomSet.diff t1.atoms t2.atoms) (Trans.(---) t1.trans t2.trans)

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


open Trans

let () =
  let n1 = mk () in
  let n2 = cons AtomSet.empty !!! (Snd n1) in
  def n1 (cons 
	    AtomSet.empty
	    !!! (Fst n2)
	 );
  let b = is_empty n1 in
  Printf.printf "is_empty=%b\n" b
