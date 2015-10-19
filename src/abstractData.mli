val enforce_no_main_locking: bool ref
(* val enforce_no_cell_locking: bool ref *)
val enforce_no_marking: bool ref

type t

val string_of: t -> string
val to_dot: t -> string

val unknown: unit -> t
(* val make: Data.t -> Lock.t -> Mark.mark -> t *)
val default: Data.t -> t

val compatible: t -> t -> bool
(* val is_consistent: int -> cell_data:t -> pattern_data:t -> bool *)
val is_consistent: cell_data:t -> pattern_data:t -> bool
val compare: t -> t -> int
val equal: t -> t -> bool
val meet: t -> t -> t
val combine: t -> t -> t
val join: t -> t -> t
val subsumes: t -> t -> bool
val is_neutral_data: t -> bool
val get_concrete_data: t -> Data.t

(* val is_not_locked: t -> bool *)
(* val is_locked_by: Lock.t -> t -> bool *)
(* val lock_by: Lock.t -> t -> t *)
(* val unlock: t -> t *)
val mark: t -> t
val deallocate: t -> t
val unmark: t -> t
val get_mark: t -> ThreeValue.t

val set_data: t -> Data.t -> t

val is_cleanable: t -> bool
