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

type 'a fstsnd = Fst of 'a | Snd of 'a
type 'a descr = {
  eps: bool;
  trans: 'a Pt.Map.t;
  def: 'a
}
type 'a nod = {
  uid: int;
  mutable undef: bool;
  mutable descr: 'a
}

module rec Descr :  Robdd.HashedOrdered with type t = Trans.t descr =
struct
  type t = Trans.t descr
  let equal n1 n2 = 
    (n1 == n2) ||
      ((n1.eps = n2.eps) &&
	 (Pt.Map.equal Trans.equal n1.trans n2.trans) && 
	 (Trans.equal n1.def n2.def))
  let hash n =
    (if n.eps then 0 else 1) +
      17 * (Trans.hash n.def) + 65537 * (Pt.Map.hash Trans.hash n.trans)

  let compare n1 n2 =
    if n1.eps != n2.eps then if n1.eps then (-1) else 1
    else let c = Trans.compare n1.def n2.def in
    if c != 0 then c else Pt.Map.compare Trans.compare n1.trans n2.trans
end 
and Trans : Robdd.S with type var = FstSnd.t = Robdd.Make(FstSnd)
and FstSnd : Robdd.HashedOrdered with type t = Descr.t nod fstsnd = 
struct
  type t = Descr.t nod fstsnd
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
end

include Descr

let cur_id = ref 0

let typ eps tr def = 
  { eps = eps; 
    def = def; 
    trans = Pt.Map.filter (fun _ d -> not (Trans.equal d def)) tr }

let any = typ true Pt.Map.empty Trans.one
let empty = typ false Pt.Map.empty Trans.zero
let eps = typ true Pt.Map.empty Trans.zero
let noneps = typ false Pt.Map.empty Trans.one

type node = Descr.t nod
let mk () =
  incr cur_id;
  { uid = !cur_id; undef = true; descr = empty }


let def n t = n.descr <- t; n.undef <- false
let get t = assert(not t.undef); t.descr
let cons t = let n = mk () in def n t; n

let inter t1 t2 = 
  typ 
    (t1.eps && t2.eps) 
    (Pt.Map.combine Trans.(&&&) t1.def t2.def t1.trans t2.trans) 
    (Trans.(&&&) t1.def t2.def)

let diff t1 t2 = 
  typ 
    (t1.eps && not t2.eps)
    (Pt.Map.combine Trans.(---) t1.def t2.def t1.trans t2.trans) 
    (Trans.(---) t1.def t2.def)

let union t1 t2 = 
  typ 
    (t1.eps || t2.eps) 
    (Pt.Map.combine Trans.(|||) t1.def t2.def t1.trans t2.trans) 
    (Trans.(|||) t1.def t2.def)

let neg t =
  typ 
    (not t.eps)
    (Pt.Map.map Trans.(~~~) t.trans)
    (Trans.(~~~) t.def)

let is_trivially_empty t = 
  not t.eps && Trans.is_zero t.def && Pt.Map.is_empty t.trans
let is_trivially_any t = 
  t.eps && Trans.is_one t.def && Pt.Map.is_empty t.trans

type v = Eps | Elt of int * v * v

exception NotEmpty

type slot = { mutable status : status; 
              mutable notify : notify;
              mutable active : bool;
	      mutable unknown : bool;
	      org: t;
	    }
and status = Empty | NEmpty of v | Maybe | Unknown
and notify = Nothing | Do of slot * (v -> unit) * notify

exception Undefined

let slot_empty = 
  { org = empty; status = Empty; active = false; notify = Nothing;
    unknown = false
  }
let slot_not_empty v = 
  { org = empty; status = NEmpty v; active = false; notify = Nothing;
    unknown = false
  }
let slot_eps = slot_not_empty Eps


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
  | { status = Unknown } -> assert false

module THash = Hashtbl.Make(Descr)
let memo = THash.create 8191
let marks = ref []

let rec slot (t : Descr.t) =
  if t.eps then slot_eps 
  else if is_trivially_empty t then slot_empty
  else
    try THash.find memo t
    with Not_found ->
      let s = { org = t; status = Maybe; active = false; notify = Nothing;
		unknown = false
	      } in
      THash.add memo t s;
      (try 
	 check_times (Pt.Map.outdomain t.trans) s t.def;
	 Pt.Map.iter (fun i x -> check_times i s x) t.trans;
         if s.active || s.unknown then marks := s :: !marks 
	 else s.status <- Empty
       with NotEmpty -> ());
      s

and check_times i s t =
  let rec aux v1 v2 accu1 accu2 t =
    Trans.decompose
      ~pos:
      (fun v t -> 
	 match v with
	   | Fst (x : node) ->
	       if x.undef then s.unknown <- true
	       else let accu1 = inter accu1 (get x) in
	       guard (slot accu1) (fun v1 -> aux v1 v2 accu1 accu2 t) s
	   | Snd x ->
	       if x.undef then s.unknown <- true
	       else let accu2 = inter accu2 (get x) in
	       guard (slot accu2) (fun v2 -> aux v1 v2 accu1 accu2 t) s)
      ~neg:
      (fun v t -> 
	 match v with
	   | Fst x ->
	       if x.undef then s.unknown <- true
	       else let accu1 = diff accu1 (get x) in
	       guard (slot accu1) (fun v1 -> aux v1 v2 accu1 accu2 t) s
	   | Snd x ->
	       if x.undef then s.unknown <- true
	       else let accu2 = diff accu2 (get x) in
	       guard (slot accu2) (fun v2 -> aux v1 v2 accu1 accu2 t) s)
      (fun () -> set s (Elt(i,v1,v2)))
      t
  in
  aux Eps Eps any any t

let rec mark_unknown s =
  s.status <- Unknown;
  THash.remove memo s.org;
  let rec aux = function
    | Nothing -> ()
    | Do (n,_,rem) -> if n.status == Maybe then mark_unknown n; aux rem
  in
  aux s.notify


let sample t =
  let s = slot t in
  List.iter
    (fun s' ->
       if s'.status == Maybe && s'.unknown then mark_unknown s')
    !marks;
  List.iter 
    (fun s' -> 
       if s'.status == Maybe then s'.status <- Empty; s'.notify <- Nothing) 
    !marks;
  marks := [];
  match s.status with 
    | Empty -> None 
    | NEmpty v -> Some v 
    | Unknown -> raise Undefined
    | Maybe -> assert false

let is_empty t = sample t == None

let is_any t = is_empty (neg t)

let sample t =
  match sample t with
    | Some v -> v 
    | None -> raise Not_found

let non_empty t = not (is_empty t)

let subset t1 t2 = is_empty (diff t1 t2)
let disjoint t1 t2 = is_empty (inter t1 t2)

let is_equal t1 t2 = subset t1 t2 && subset t2 t1

let fst n = 
  if not (n.undef) && (is_trivially_any (get n)) then noneps
  else typ false Pt.Map.empty (Trans.(!!!) (Fst n))
let snd n =
  if not (n.undef) && (is_trivially_any (get n)) then noneps
  else typ false Pt.Map.empty (Trans.(!!!) (Snd n))
let tag i = 
  typ false (Pt.Map.singleton i Trans.one) Trans.zero
let tag_in ts =
  typ false (Pt.Map.constant ts Trans.one) Trans.zero
let tag_not_in ts =
  typ false (Pt.Map.constant ts Trans.zero) Trans.one
let nottag i = 
  typ false (Pt.Map.singleton i Trans.zero) Trans.one

let get_trans t i =
  try Pt.Map.find i t.trans
  with Not_found -> t.def

let dnf_trans t =
  let res = ref [] in
  let rec aux accu1 accu2 t =
    Trans.decompose
      ~pos:
      (fun v t -> 
	 match v with
	   | Fst x ->
	       let accu1 = inter accu1 (get x) in
	       if non_empty accu1 then aux accu1 accu2 t
	   | Snd x ->
	       let accu2 = inter accu2 (get x) in
	       if non_empty accu2 then aux accu1 accu2 t)
      ~neg:
      (fun v t -> 
	 match v with
	   | Fst x ->
	       let accu1 = diff accu1 (get x) in
	       if non_empty accu1 then aux accu1 accu2 t
	   | Snd x ->
	       let accu2 = diff accu2 (get x) in
	       if non_empty accu2 then aux accu1 accu2 t)
      (fun () -> res := (accu1,accu2)::!res)
      t
  in
  aux any any t;
  !res

let dnf_neg_pair i t = dnf_trans (Trans.(~~~) (get_trans t i))

let dnf_neg_all t =
  Pt.Map.domain t.trans,
  dnf_trans (Trans.(~~~) t.def),
  Pt.Map.fold (fun i x accu -> (i, dnf_trans (Trans.(~~~) x)) :: accu) 
    t.trans []


let rec is_in v t = match v with
  | Eps -> t.eps
  | Elt (i,v1,v2) ->
      List.exists 
	(fun (t1,t2) -> is_in v1 t1 && is_in v2 t2) 
	(dnf_trans (get_trans t i))


let dump_tr l ppf = function
  | Fst x -> l := x::!l; Format.fprintf ppf "L%i" x.uid
  | Snd x -> l := x::!l; Format.fprintf ppf "R%i" x.uid

let print_tag ppf i = 
  try 
    let s = Hashtbl.find rev_tags i in
    Format.fprintf ppf "%s" s
  with Not_found -> Format.fprintf ppf "%i" i

let rec print_tags ppf = function
  | [i] -> print_tag ppf i
  | i::l -> Format.fprintf ppf "%a|" print_tag i; print_tags ppf l
  | [] -> assert false
  

let print ppf t =
  let l = ref [] in
  let p = ref [] in
  let rec descr t =
    let first = ref true in
    let sep () = if !first then first := false else Format.fprintf ppf " | " in
    if t.eps then (sep (); Format.fprintf ppf "()");
    
    let h = ref Pt.Map.empty in
    Pt.Map.iter
      (fun i f ->
	 let id = Trans.uid f in
	 let l = 
	   try Pervasives.snd (Pt.Map.find id !h)
	   with Not_found -> []
	 in
	 h := Pt.Map.add id (f,i::l) !h
      ) t.trans;
    
    Pt.Map.iter
      (fun _ (f,tags) ->
	 if not (Trans.is_zero f) then (
	   sep ();
	   Format.fprintf ppf "%a[%a]" 
	     print_tags (List.sort Pervasives.compare tags)
	     (Trans.print_formula (dump_tr l)) (Trans.formula f)
	 )
      )
      !h;

    if not (Trans.is_zero t.def) then (
      sep ();
      Format.fprintf ppf "*[%a]" 
	(Trans.print_formula (dump_tr l)) (Trans.formula t.def)
    )
  and loop () = match !l with [] -> () | t::rest ->
    l := rest;
    if List.memq t !p then ()
    else (
      p := t :: !p;
      Format.fprintf ppf "%i:=" t.uid;
      if t.undef then Format.fprintf ppf "UNDEF" else descr (get t);
      Format.fprintf ppf "@."
    );
    loop ()
  in
  descr t;
  Format.fprintf ppf "@.";
  loop ()


(*
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
*)


let rec print_v ppf = function
  | Elt (i,v1,v2) -> 
      Format.fprintf ppf "%a[%a]%a" 
	print_tag i print_v_content v1 print_v_rest v2
  | Eps -> Format.fprintf ppf "()"
and print_v_content ppf = function
  | Eps -> ()
  | x -> Format.fprintf ppf "%a" print_v x
and print_v_rest ppf = function
  | Eps -> ()
  | x -> Format.fprintf ppf ",%a" print_v x


let elt i t1 t2 =
  inter (tag i) (inter (fst t1) (snd t2))

let rec singleton = function
  | Eps -> eps
  | Elt (i,v1,v2) -> elt i (cons (singleton v1)) (cons (singleton v2))

let is_defined t =
  let seen = ref Pt.Set.empty in
  let rec check_tr tr =
    let id = Trans.uid tr in 
    if not (Pt.Set.mem id !seen) then
      let () = seen := Pt.Set.add id !seen in
      Trans.iter
	(function Fst x | Snd x -> if x.undef then raise Exit; check_t (get x))
	tr
  and check_t x =
    check_tr x.def;
    Pt.Map.iter (fun _ tr -> check_tr tr) x.trans
  in
  try check_t t; true
  with Not_found -> false
