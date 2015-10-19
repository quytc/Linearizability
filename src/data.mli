
(** Data in the system. *)

type t

val mk: char -> t
val reconstruct: int * char -> t

val bottom: t
val top: t
val neutral: t

val unpack: t -> int
val char_of: t -> char
val string_of: t -> string
val buffer: Buffer.t -> t -> unit
val color: char -> string

val equal: t -> t -> bool
val compare: t -> t -> int

val is_interesting: t -> bool

val compatible: t -> t -> bool

val is_cleanable: t -> bool
