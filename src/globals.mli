
val progress: bool ref
val print_progress: int -> int -> unit
val results: bool ref
val results_dir: string ref
val trace: bool ref

val nullpointer_dereferencing: bool ref
val danglingpointer: bool ref
val free_dereferencing: bool ref
val doublefree: bool ref
val cycle: bool ref

val get_options: unit -> string

val mkdir: string -> unit
(** mkdir [name] creates a directory (and any subdirectories if necessary). [name] must be escaped. *)
