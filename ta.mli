type atom = int

type t
val hash: t -> int
val equal: t -> t -> bool
val compare: t -> t -> int

(** Boolean combinations *)
val any: t
val empty: t
val inter: t -> t -> t
val union: t -> t -> t
val diff: t -> t -> t
val neg: t -> t

val is_trivially_empty: t -> bool
val is_trivially_any: t -> bool

(** Sets of pairs. *)
val any_pair: t  (** Any pair. *)
val fst: t -> t  (** Any pair whose first component is as given. *)
val snd: t -> t  (** Any pair whose second component is as given. *)

(** Sets of atoms. *)
val any_atom: t
val atom: atom -> t

(** Delayed creation. *)
type delayed
val mk: unit -> delayed
val def: delayed -> t -> unit
val get_delayed: delayed -> t

(** Emptyness check. *)
val is_empty: t -> bool
val subset: t -> t -> bool
val disjoint: t -> t -> bool

type v = Atom of atom | Pair of v * v
val is_in: v -> t -> bool

val dnf_pair: t -> (t * t) list
val dnf_neg_pair: t -> (t * t) list
