
module LT : Hashtbl.S with type key = Label.t
module LS : Set.S with type elt = Label.t
val string_of_labels: LS.t -> string

module Vertex : sig

  type t

  val empty: unit -> t
  val clone: t -> t

  val to_dot: t -> int -> string -> string
      
  val add_label: t -> Label.t -> unit
  val remove_label: t -> Label.t -> unit

  val is_cleanable: t -> bool
  val is_simple: t -> bool
  val is_leaf: t -> bool

  val get_data: t -> Data.t
  val set_data: t -> Data.t -> unit
  val reset_data: t -> unit
      
  val deallocate: t -> unit
  val allocate: t -> unit
  val allocation: t -> bool
  val is_deallocated: t -> bool
end

type t
type vertex = Vertex.t

val create: unit -> t
val clone: t -> t

val nb_vertex: t -> int
val iter_vertex: t -> ( int -> vertex -> unit ) -> unit
val fold_vertex: t -> 'a -> ( 'a -> int -> vertex -> 'a) -> 'a

val get: t -> int -> vertex
val get_node: t -> Label.t -> int
val succ: t -> int -> int

val vbottom: int
val vnil: int

val has_cycle: t -> bool

val add_label: t -> int -> Label.t -> unit
val remove_label: t -> int -> Label.t -> unit
    
val add_vertex: t -> vertex -> int
val add_edge: t -> int -> int -> unit
val redirect_edge: t -> int -> int -> unit
(* val add_vertex_in_edge: t -> int -> int -> int *)

val clean_vertex: t -> int -> vertex -> unit
    
val order: string -> string -> int
val encode: t -> string array -> string

val check: t -> bool
