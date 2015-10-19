(* ========================================================================================================= *)
(* =====================             Set of minimal elements                        ======================== *)
(* ========================================================================================================= *)

module type Encoded = sig
  type t
  val equal: t -> t -> bool
  val hash: t -> int
end

module type S_sig = sig

  type elt
  type t

  val size: t -> int
(*   val real_size: t -> int *)
      
  val insert: t -> elt -> bool
    (** [insert s x] returns [true] if [x] was inserted in [s], [false] otherwise. *)

  val create: unit -> t
    (** Creates an empty set. *)
      
  val is_empty: t -> bool
  val to_list: t -> elt list
      
  val iter: t -> (elt -> unit) -> unit
    (** [iter f s] iterates [f] over all elements of [s]. *)
      
  val fold: ('a -> elt -> 'a) -> 'a -> t -> 'a
      
(*   val iter_cond: (elt -> bool) -> t -> elt option *)
(*     (\** [iter_cond f cs] applies [f] to each elements of [cs], breaks when [f] returns [false] and returns that element. *)
(*        Otherwise, it returns [None]. *\) *)

  val mem: t -> elt -> bool

  val clear: t -> unit
    (** [clear s] removes every element from [s]. *)

end
(** Output signature of the functor of Minset. *)


module Basic (E: Encoded) : S_sig with type elt = E.t
