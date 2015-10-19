(** 
    iterate through injections from one set_S to set_B.

   Every instance must:
   - call [init] to place the iterator on a correct injection (eventually non existing)
   - first check [hasMore] before it calls [get].

   Todo: Make it start from the natural injection ( 1 -> 1, 2 -> 2, ...).
*)


class ordered_cyclic_injections: int -> int ->
  object
    method init: unit
    method next: unit
    method get: int array
    method hasMore: bool
    method print: unit
  end
    
class powerinjections: int -> int ->
  object
    method init: unit
    method next: unit
    method get: ( (int option) * (int option) ) list
    method hasMore: bool
    method print: unit
  end

class injections: int -> int ->
  object
    method init: unit
    method next: unit
    method get: int array
    method hasMore: bool
    method print: unit
  end


type mapping = (int option) * (int option)
exception NotCached
class ['a] cache: int -> int -> 
object
  method get: mapping -> 'a
  method set: mapping -> 'a -> unit
  method print: ('a -> unit) -> unit
end


class ['a] powerset: 'a list ->
object
  method hasMore: bool
  method next: unit
  method get: 'a list
end

val permute: 'a list -> 'a list list
