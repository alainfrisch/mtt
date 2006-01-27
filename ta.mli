type atom = int

val atom_of_string: string -> atom

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

val eps: t
val fst: t -> t  (** Any pair whose first component is as given. *)
val snd: t -> t  (** Any pair whose second component is as given. *)
val elt: atom -> t -> t -> t
val tag: atom -> t
val nottag: atom -> t
val noneps: t
val tag_in: Pt.Set.t -> t
val tag_not_in: Pt.Set.t -> t

(** Delayed creation. *)
type delayed
val mk: unit -> delayed
val def: delayed -> t -> unit
val get_delayed: delayed -> t

val is_defined: t -> bool

(** Emptyness check. *)
exception Undefined
val is_empty: t -> bool
val is_any: t -> bool
val subset: t -> t -> bool
val disjoint: t -> t -> bool

type v = Eps | Elt of atom * v * v
val is_in: v -> t -> bool

(*
val dnf_pair: t -> (t * t) list
*)

val dnf_neg_pair: atom -> t -> (t * t) list
val dnf_neg_all: t -> Pt.Set.t * (t * t) list * (atom * (t * t) list) list


val print: Format.formatter -> t -> unit

(*
val normalize: t -> t
val normalize2: t -> t
*)

val sample: t -> v
val print_v:  Format.formatter -> v -> unit


val singleton: v -> t
