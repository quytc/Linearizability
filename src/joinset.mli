module type S = sig
  type t
  val compare: t -> t -> bool
end