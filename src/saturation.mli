module type P_Sig = sig

  type p
  exception InconsistentExn
  module V : sig
    type t
    val equal: t -> t -> bool
    val compare: t -> t -> int
    val string_of: t -> string
    val has_globals: t -> bool
    val equal_data: t -> t -> bool
    val is_dirty: t -> bool
    val is_dirty_and_colored: t -> bool
    val make_dirty: t -> unit
    val must_local: t -> bool
    val make_local: t -> unit
    val is_eventually_deallocated: t -> bool
    val is_deallocated: t -> bool
    val make_allocated: t -> unit
    val make_deallocated: t -> unit
  end
  type vertex = V.t
  type edge = Label.Edge.t
  module E : sig
    val anti: edge -> edge
    val string_of: vertex -> vertex -> edge -> string
  end
 
  val are_explicitly_not_equal: p -> vertex -> vertex -> bool
  val get_vertex: p -> Label.t -> vertex
  val find_vertex: p -> vertex -> vertex
  val get_succ: p -> vertex -> vertex option
  val is_inconsistent: ?force:bool -> p -> bool
  val clean: p -> unit
  val to_dot: p -> string -> unit
  val vbottom: p -> vertex
  val vnil: p -> vertex
  val log_message: p -> string -> unit
  val string_of: p -> string
  val id: p -> int
      
  val add_vertex: p -> vertex -> unit
  val remove_vertex: p -> vertex -> unit
  val mem_edge: p -> vertex -> vertex -> edge -> bool
  val add_edge: p -> vertex -> vertex -> edge -> bool

  val remove_edge: p -> vertex -> vertex -> edge -> unit
  val iter_vertex: p -> (vertex -> unit) -> unit

  val iter_edges: p -> (vertex -> vertex -> edge -> unit) -> unit
  val iter_edge: p -> edge -> (vertex -> vertex -> unit) -> unit
  val succ: p -> vertex -> edge -> vertex list
  val pred: p -> vertex -> edge -> vertex list
  val iter_succ: p -> vertex -> edge -> (vertex -> unit) -> unit
  val iter_pred: p -> vertex -> edge -> (vertex -> unit) -> unit

  val clone: p -> p
  val get_cycle: p -> vertex -> edge -> vertex list
  val merge_vertices: p -> remove:vertex -> replace:vertex -> unit
  val make_not_equal: p -> vertex -> vertex -> bool
end

module type Sat_sig = sig
  type elt
  val apply: elt -> elt list
  val apply_next: elt -> Label.t -> Label.t -> elt list
end

module Make (P : P_Sig) : Sat_sig with type elt = P.p
