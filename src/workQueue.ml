
exception Empty
exception ObserverSaturated

type 'a t = {
    heap: 'a Queue.t array;(* All the queues per priority *)
    mutable max_size: int;
    max: int;       (* Just the number of priorities, to iterate the queues *)
    mutable min: int;       (* the lowest priority *)
    priority: 'a -> int; (* the hashing function *)
  }

let create hash nb = {
  heap       = Array.init nb (fun _ -> Queue.create ());
  max        = nb-1;
  min        = 0;
  priority   = hash;
  max_size   = 1;
}

let max_size h = h.max_size
let size h = Array.fold_left (fun n q -> n+Queue.length q) 0 h.heap
let size_prio prio h = Queue.length h.heap.(prio)

(* let rec pick prio h =  *)
(*   if prio > h.max then raise Empty; *)
(*   try Queue.take h.heap.(prio) *)
(*   with Queue.Empty -> pick (prio+1) h *)

(* let take h = pick 0 h *)

let rec take h =
  if h.min > h.max then raise Empty;
  if Queue.is_empty h.heap.(h.min) then (h.min <- h.min+1;raise ObserverSaturated) else Queue.take h.heap.(h.min)

let add e h = begin
  let prio = h.priority e in
  if h.min > prio then h.min <- prio;
  h.max_size <- h.max_size + 1;
  Queue.add e h.heap.(prio)
end

let iter f h = Array.iter (Queue.iter f) h.heap

let min h = h.min
