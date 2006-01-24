type atom = int

let tags = Hashtbl.create 64
let rev_tags = Hashtbl.create 64
let tag_id = ref 0
let atom_of_string x =
  try Hashtbl.find tags x
  with Not_found ->
    incr tag_id;
    Hashtbl.add tags x !tag_id;
    Hashtbl.add rev_tags !tag_id x;
    !tag_id


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

  let sample = function
    | Finite s -> Pt.Set.choose s
    | Cofinite s -> if Pt.Set.is_empty s then 0 else succ (Pt.Set.max_elt s)

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

  let equal s1 s2 =
    match s1,s2 with
      | Finite s1, Finite s2
      | Cofinite s1, Cofinite s2 -> Pt.Set.equal s1 s2 
      | _ -> false 

  let hash = function
    | Finite s -> 1 + 2 * Pt.Set.hash s
    | Cofinite s -> 2 * Pt.Set.hash s

  let compare s1 s2 = Pervasives.compare s1 s2
end

type 'a fstsnd = Fst of 'a | Snd of 'a
type 'a node = {
  uid: int;
  mutable atoms: AtomSet.t;
  mutable trans: 'a;
  mutable undef: bool;
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
    | Fst _, Snd _ -> -1
    | Snd _, Fst _ -> 1 
(*  let compare x y = match x,y with
    | (Fst n1 | Snd n1), (Fst n2 | Snd n2) ->
	if n1 == n2 then match x,y with
	  | Fst _, Fst _ | Snd _, Snd _ -> 0
	  | Fst _, Snd _ -> 1 | _ -> -1
	else n2.uid - n1.uid  *)
end

include Node

let cur_id = ref 0

let typ atoms tr = 
  incr cur_id; { uid = !cur_id; atoms = atoms; trans = tr; undef = false }

let any = typ AtomSet.any Trans.one
let empty = typ AtomSet.empty Trans.zero
let any_pair = typ AtomSet.empty Trans.one
let any_atom = typ AtomSet.any Trans.zero

type delayed = t

let mk () = 
  let t = typ AtomSet.any Trans.one in
  t.undef <- true;
  t

let def n t = 
(*  let tr = if AtomSet.is_any t.atoms && 
    Trans.check_var (function Fst m | Snd m -> n == m) t.trans then
      Trans.one else t.trans in *)
  let tr = t.trans in
  (*assert(n.undef); *) n.atoms <- t.atoms; n.trans <- tr; n.undef <- false
let get_delayed t = t

let inter t1 t2 = 
  typ (AtomSet.inter t1.atoms t2.atoms) (Trans.(&&&) t1.trans t2.trans)
let diff t1 t2 = 
  typ (AtomSet.diff t1.atoms t2.atoms) (Trans.(---) t1.trans t2.trans)
let union t1 t2 = 
  typ (AtomSet.union t1.atoms t2.atoms) (Trans.(|||) t1.trans t2.trans)
let neg t =
  typ (AtomSet.neg t.atoms) (Trans.(~~~) t.trans)

let is_trivially_empty t = 
  not t.undef && Trans.is_zero t.trans && AtomSet.is_empty t.atoms
let is_trivially_any t = 
  not t.undef && Trans.is_one t.trans && AtomSet.is_any t.atoms

(*
let dnf_trans =
  Trans.dnf_enum
    (fun x accu -> x :: accu)
    ~pos:(fun x (fst,snd) -> match x with
	    | Fst t ->  inter fst t, snd
	    | Snd t -> fst, inter snd t)
    ~neg:(fun x (fst,snd) -> match x with
	    | Fst t -> diff fst t, snd
	    | Snd t -> fst, diff snd t)
    [] (any,any)
*)


type v = Atom of atom | Pair of v * v

exception NotEmpty

type slot = { mutable status : status; 
              mutable notify : notify;
              mutable active : bool }
and status = Empty | NEmpty of v | Maybe
and notify = Nothing | Do of slot * (v -> unit) * notify

let slot_empty = { status = Empty; active = false; notify = Nothing }
let slot_not_empty v = { status = NEmpty v; active = false; notify = Nothing }

let rec notify v = function
  | Nothing -> ()
  | Do (n,f,rem) -> 
      if n.status == Maybe then (try f v with NotEmpty -> ());
      notify v rem

let set s v =
  s.status <- NEmpty v;
  notify v s.notify;
  s.notify <- Nothing; 
  raise NotEmpty

let guard a f n = match a with
  | { status = Empty } -> ()
  | { status = Maybe } as s -> n.active <- true; s.notify <- Do (n,f,s.notify)
  | { status = NEmpty v } -> f v


module TransHash = Hashtbl.Make(Trans)
let memo = TransHash.create 8191
let marks = ref []
let count = ref 0

let rec slot t =
  if t.undef then (print_endline "XXX\n"; exit 3);
  if not (AtomSet.is_empty t.atoms) 
  then slot_not_empty (Atom (AtomSet.sample t.atoms))
  else
    let tr = t.trans in
    if Trans.is_zero tr then slot_empty
    else if Trans.is_one tr then slot_not_empty (Pair (Atom 0, Atom 0))
    else try TransHash.find memo tr
    with Not_found ->
      incr count;
(*      if (!count mod 1000 = 0) then (print_char '.'; flush stdout); *)
(*      if !count > 80 then
	Format.fprintf Format.std_formatter "[%i]=>%a@." !count
	  (Trans.print_formula (fun ppf -> function
				  | Fst x -> Format.fprintf ppf "L%i" x.uid
				  | Snd x -> Format.fprintf ppf "R%i" x.uid))
	  (Trans.formula tr); *)
      let s = { status = Maybe; active = false; notify = Nothing } in
      TransHash.add memo tr s;
      (try 
	 check_times s tr;
         if s.active then marks := s :: !marks else s.status <- Empty
       with NotEmpty -> ());
      s

and check_times s t =
  let rec aux v1 v2 accu1 accu2 t =
    Trans.decompose
      ~pos:
      (fun v t -> 
	 match v with
	   | Fst x ->
	       let accu1 = inter accu1 x in
	       guard (slot accu1) (fun v1 -> aux v1 v2 accu1 accu2 t) s
	   | Snd x ->
	       let accu2 = inter accu2 x in
	       guard (slot accu2) (fun v2 -> aux v1 v2 accu1 accu2 t) s)
      ~neg:
      (fun v t -> 
	 match v with
	   | Fst x ->
	       let accu1 = diff accu1 x in
	       guard (slot accu1) (fun v1 -> aux v1 v2 accu1 accu2 t) s
	   | Snd x ->
	       let accu2 = diff accu2 x in
	       guard (slot accu2) (fun v2 -> aux v1 v2 accu1 accu2 t) s)
      (fun () -> set s (Pair(v1,v2)))
      t
  in
  aux (Atom 0) (Atom 0) any any t

let sample t =
  let s = slot t in
  List.iter 
    (fun s' -> 
       if s'.status == Maybe then s'.status <- Empty; s'.notify <- Nothing) 
    !marks;
  marks := [];
  match s.status with 
    | Empty -> None 
    | NEmpty v -> Some v 
    | Maybe -> assert false

let is_empty t = sample t == None

let is_any t = is_empty (neg t)

let sample t =
  match sample t with
    | Some v -> v 
    | None -> raise Not_found

let non_empty t = not (is_empty t)

let dnf_trans t =
  let res = ref [] in
  let rec aux accu1 accu2 t =
    Trans.decompose
      ~pos:
      (fun v t -> 
	 match v with
	   | Fst x ->
	       let accu1 = inter accu1 x in
	       if non_empty accu1 then aux accu1 accu2 t
	   | Snd x ->
	       let accu2 = inter accu2 x in
	       if non_empty accu2 then aux accu1 accu2 t)
      ~neg:
      (fun v t -> 
	 match v with
	   | Fst x ->
	       let accu1 = diff accu1 x in
	       if non_empty accu1 then aux accu1 accu2 t
	   | Snd x ->
	       let accu2 = diff accu2 x in
	       if non_empty accu2 then aux accu1 accu2 t)
      (fun () -> res := (accu1,accu2)::!res)
      t
  in
  aux any any t;
  !res



(*
let is_empty t =
  Printf.eprintf "+"; flush stderr;
  let r = is_empty t in
  Printf.eprintf "-"; flush stderr;
  r
*)

let subset t1 t2 = is_empty (diff t1 t2)
let disjoint t1 t2 = is_empty (inter t1 t2)

let is_equal t1 t2 = subset t1 t2 && subset t2 t1

let fst t = 
  if not (t.undef) && (is_trivially_any t) then any_pair
  else typ AtomSet.empty (Trans.(!!!) (Fst t))
let snd t =
  if not (t.undef) && (is_trivially_any t) then any_pair
  else typ AtomSet.empty (Trans.(!!!) (Snd t))
let atom i = typ (AtomSet.singleton i) Trans.zero

let dnf_pair t = dnf_trans t.trans

let dnf_neg_pair t = dnf_trans (Trans.(~~~) t.trans)


let rec is_in v t = match v with
  | Atom i -> AtomSet.is_in i t.atoms
  | Pair (v1,v2) -> 
      List.exists 
	(fun (t1,t2) -> is_in v1 t1 && is_in v2 t2) 
	(dnf_pair t)  (* todo: don't build the dnf here *)


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
	    if t.undef then Format.fprintf ppf "%i:=UNDEF@." t.uid
	    else
(*	    if is_empty t then Format.fprintf ppf "%i:=Empty@." t.uid
	    else if is_equal t any then Format.fprintf ppf "%i:=Any@." t.uid
	    else if is_equal t any_atom then 
	      Format.fprintf ppf "%i:=AnyAtom@." t.uid
	    else if is_equal t any_pair then 
	      Format.fprintf ppf "%i:=AnyPair@." t.uid
	    else   *)
	    Format.fprintf ppf "%i:={atoms:%a;pairs:%a}@." t.uid
	      AtomSet.print t.atoms
(*		(Trans.dump_dnf (dump_tr l)) t.trans *)
	      (Trans.print_formula (dump_tr l)) (Trans.formula t.trans)
(*	      (Trans.dump (dump_tr l)) t.trans   *)
	  );
	  flush stdout;
	  loop ()
  in
  loop ()


let normalize_dnf l =
  let rec add accu t1 t2 = function
    | [] -> (t1,t2) :: accu
    | ((s1,s2) as s)::rest ->
	if disjoint s1 t1 then add (s::accu) t1 t2 rest
	else
	  let t1' = inter t1 s1 in
	  let accu = (t1',union t2 s2) :: accu in
	  let s1' = diff s1 t1 in
	  let accu = if is_empty s1' then accu else (s1',s2) :: accu in
	  let t1 = diff t1 s1 in
	  if is_empty t1 then accu @ rest
	  else add accu t1 t2 rest
  in
  List.fold_left (fun accu (t1,t2) -> add [] t1 t2 accu) [] l
	    
    

module Memo = Hashtbl.Make(Node)

let normalize_memo = Memo.create 4096

let rec normalize t =
  try Memo.find normalize_memo t
  with Not_found ->
(*    Format.fprintf Format.std_formatter "Normalize (uid=%i):%a@." 
      (Trans.uid t.trans)
      print t; *)
    let t' = mk () in
    Memo.add normalize_memo t t';
    t'.atoms <- t.atoms;
    t'.trans <- 
      List.fold_left
      (fun accu (t1,t2) ->
	 Trans.(|||) accu 
	   (Trans.(&&&) (Trans.(!!!) (Fst (normalize t1)))
	      (Trans.(!!!) (Snd (normalize t2))))
      )
      Trans.zero
      ((*normalize_dnf*) (dnf_trans t.trans));
      t'.undef <- false;
(*    Memo.add normalize_memo t' t'; *)
    t'

let normalize2_memo = Memo.create 4096

let rec normalize2 t =
  try Memo.find normalize2_memo t
  with Not_found ->
(*    Format.fprintf Format.std_formatter "Normalize (uid=%i):%a@." 
      (Trans.uid t.trans)
      print t; *)
    let t' = mk () in
    Memo.add normalize2_memo t t';
    t'.atoms <- t.atoms;
    t'.trans <- 
      List.fold_left
      (fun accu (t1,t2) ->
	 Trans.(|||) accu 
	   (Trans.(&&&) (Trans.(!!!) (Fst (normalize2 t1)))
	      (Trans.(!!!) (Snd (normalize2 t2))))
      )
      Trans.zero
      (normalize_dnf (dnf_trans t.trans));
    t'.undef <- false;
    Memo.add normalize2_memo t' t';
    t'

(*
let rec sample seen t =
  if not (AtomSet.is_empty t.atoms) then Atom (AtomSet.sample t.atoms)
  else
    let uid = Trans.uid t.trans in
    if Pt.Set.mem uid seen then raise Not_found
    else let seen = Pt.Set.add uid seen in
    let rec aux = function
      | [] -> raise Not_found
      | (t1,t2)::rest ->
	  if is_empty t1 || is_empty t2 then aux rest else
	  try Pair (sample seen t1, sample seen t2)
	  with Not_found -> aux rest
    in
    aux (dnf_trans t.trans)

let sample = sample Pt.Set.empty
*)

let rec print_v ppf = function
  | Atom i -> 
      (try 
	 let s = Hashtbl.find rev_tags i in
	 Format.fprintf ppf "%s" s
       with Not_found -> Format.fprintf ppf "%i" i)
  | Pair (v1,v2) -> Format.fprintf ppf "(%a,%a)" print_v v1 print_v v2


let rec singleton = function
  | Atom i -> atom i
  | Pair (v1,v2) -> inter (fst (singleton v1)) (snd (singleton v2))
