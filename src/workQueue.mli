
type 'a t
exception Empty
exception ObserverSaturated
val max_size: 'a t -> int
val size: 'a t -> int
val size_prio: int -> 'a t -> int
val add: 'a -> 'a t -> unit
val take: 'a t -> 'a
val create: ('a -> int) -> int -> 'a t
val iter: ('a -> unit) -> 'a t -> unit
val min: 'a t -> int
