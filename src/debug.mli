(* external get_time: unit -> int = "caml_get_time" *)
(* external delta_to_usec: int -> int = "caml_delta_to_usec" *)

val level: int -> unit

val pause: string -> unit
(* val pause: (Format.formatter -> 'a -> unit) -> unit *)

val print: ('a, out_channel, unit) format -> 'a
(* val print: ('a, Format.formatter, unit) format -> 'a *)

val red: string
val blue: string
val green: string
val fuschia: string 
val yellow: string
val noColor: string

val serialize: 'a -> string -> unit
