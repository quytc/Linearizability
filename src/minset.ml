let sprintf = Printf.sprintf

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
  val insert: t -> elt -> bool
  val create: unit -> t
  val is_empty: t -> bool
  val to_list: t -> elt list
  val iter: t -> (elt -> unit) -> unit
  val fold: ('a -> elt -> 'a) -> 'a -> t -> 'a
  val mem: t -> elt -> bool
  val clear: t -> unit
end

module Basic (E: Encoded) : S_sig with type elt = E.t
      =
  struct

    let debug = Debug.minset

    type elt = E.t

    module HT = Hashtbl.Make(E)

    type t = unit HT.t	
  
    let create () = HT.create 49999

    let size = HT.length

    let is_empty (c:t) = size c = 0
	
    let iter (c:t) (f: elt -> unit) : unit = HT.iter (fun v _ -> f v) c

    let fold (f: 'a -> elt -> 'a) (acc:'a) (c:t) = HT.fold (fun v _ acc -> f acc v) c acc

    let is_minimal _ = true

    let insert (c:t) (element:elt) : bool = begin
      if HT.mem c element
      then false
      else begin
	HT.add c element ();
	true
      end
    end

    let mem = HT.mem

    let to_list c = fold (fun acc el -> el::acc) [] c

    let clear = HT.clear

  end
