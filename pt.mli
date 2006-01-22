(* Sets and maps over integer implemented as Patricia trees.
   Code borrowed from J.C. Filliatre. *)

module Set : sig
  type t
  
  type elt = int
      
  val empty : t
    
  val is_empty : t -> bool
    
  val mem : int -> t -> bool
    
  val add : int -> t -> t
    
  val singleton : int -> t
    
  val remove : int -> t -> t
    
  val union : t -> t -> t
    
  val subset : t -> t -> bool
    
  val inter : t -> t -> t
    
  val diff : t -> t -> t
    
  val equal : t -> t -> bool
    
  val compare : t -> t -> int
    
  val elements : t -> int list
    
  val choose : t -> int
    
  val cardinal : t -> int
    
  val iter : (int -> unit) -> t -> unit
    
  val fold : (int -> 'a -> 'a) -> t -> 'a -> 'a
    
  val for_all : (int -> bool) -> t -> bool
    
  val exists : (int -> bool) -> t -> bool
    
  val filter : (int -> bool) -> t -> t
    
  val partition : (int -> bool) -> t -> t * t
    
  val split : int -> t -> t * bool * t
    
  (*s Warning: [min_elt] and [max_elt] are linear w.r.t. the size of the
    set. In other words, [min_elt t] is barely more efficient than [fold
    min t (choose t)]. *)
    
  val min_elt : t -> int
  val max_elt : t -> int
    
  (*s Additional functions not appearing in the signature [Set.S] from ocaml
    standard library. *)
    
  (* [intersect u v] determines if sets [u] and [v] have a non-empty 
     intersection. *) 
    
  val intersect : t -> t -> bool
    
    
  val hash : t -> int
end

module Map : sig
  type (+'a) t

  type key = int

  val empty : 'a t
    
  val is_empty : 'a t -> bool
    
  val singleton : int -> 'a -> 'a t
    
  val add : int -> 'a -> 'a t -> 'a t
    
  val find : int -> 'a t -> 'a
    
  val remove : int -> 'a t -> 'a t
    
  val mem :  int -> 'a t -> bool
    
  val iter : (int -> 'a -> unit) -> 'a t -> unit
    
  val map : ('a -> 'b) -> 'a t -> 'b t
    
  val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
    
  val fold : (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    
  val set : int -> ('a option -> 'a) -> 'a t -> 'a t
    
  val unset : int -> ('a -> 'a option) -> 'a t -> 'a t
    
  val hash : ('a -> int) -> 'a t -> int
    
  val subset : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
    
  val union : ('a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
    
  val is_singleton : ('a -> 'b option) -> 'a t -> 'b option
    
  val disjoint : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    
  val diff : ('a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t

  val restrict  : 'a t -> Set.t -> 'a t
end
