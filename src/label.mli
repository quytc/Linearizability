
(** Variables in the system. *)

type op
type r
type t

val equal: t -> t -> bool
val hash: t -> int
val compare: t -> t -> int

(** [global s] returns a fresh flagged label. *)
val global: int * string *int -> t
(** [local s] returns a fresh flagged label. *)
val local: int * string * int -> t

val is_global: t -> bool
val is_elim_global: t -> bool
val is_main_global: t -> bool 
  val is_lock_global: t -> bool  
val is_local: t -> bool
val is_new: t -> bool
val unpack: t -> int
val string_of: t -> string

val nil: t
val bottom: t
val free: t
val locked: t
