let sprintf = Printf.sprintf 

(* let enforce_no_cell_locking = ref false *)
let enforce_no_main_locking = ref false
let enforce_no_marking = ref false

module Mark = struct
  type t = ThreeValue.t
  let to_dot = function ThreeValue.Yes -> " | ✔" | ThreeValue.No -> "" | _ -> " | ?"
  let string_of = function ThreeValue.Yes -> " | marked" | ThreeValue.No -> " | unmarked" | _ -> " | dunno"
  let make m = if !enforce_no_marking then ThreeValue.No else m
  let default = make ThreeValue.No
  let unknown = make ThreeValue.Maybe
  let compatible = ThreeValue.compatible
  let compare m1 m2 = if !enforce_no_marking then 0 else ThreeValue.compare m1 m2
  let meet m1 m2 = if !enforce_no_marking then ThreeValue.No else ThreeValue.meet m1 m2
  let join = meet
  let subsumes = ThreeValue.entails
  let is_cleanable _ = true
  let mark _ = if !enforce_no_marking then failwith("Que? Using marks for mark free stuff?") else ThreeValue.Yes
  let unmark _ = if !enforce_no_marking then failwith("Que? Using marks for mark free stuff?") else ThreeValue.No
  let get_mark v = v
end

type t = Data.t * Mark.t

let string_of (d,m) = sprintf "%s%s" (Data.string_of d) (if !enforce_no_marking then "" else Mark.string_of m)

let to_dot (d,m) = sprintf "%s%s" (Data.string_of d) (if !enforce_no_marking then "" else Mark.to_dot m)

let unknown _ = Data.neutral,(if !enforce_no_marking then Mark.default else Mark.unknown)

let default color = color,Mark.default

let compatible (data1,mark1) (data2,mark2) =
  Data.compatible data1 data2 &&
  (if !enforce_no_marking then true else Mark.compatible mark1 mark2)

let is_consistent ~cell_data:(data1,mark1) ~pattern_data:(data2,mark2) =
  Data.compatible data1 data2 &&
  (if !enforce_no_marking then true else Mark.compatible mark1 mark2)

let compare (d1,m1) (d2,m2) : int =
  let cv = Data.compare d1 d2 in
  if cv <> 0 then cv else if !enforce_no_marking then 0 else Mark.compare m1 m2

let equal data1 data2 = compare data1 data2 = 0

let meet (data1,m1) (data2,m2) = (Data.meet data1 data2), (Mark.meet m1 m2)
let combine (data1,m1) (data2,m2) = (Data.meet data1 data2), (Mark.meet m1 m2)
    
let join (data1,m1) (data2,m2) = (Data.join data1 data2), (Mark.join m1 m2)
      
let subsumes (data1,m1) (data2,m2) =
  Data.subsumes data1 data2 &&
  (if !enforce_no_marking then true else Mark.subsumes m1 m2)

let is_neutral_data (data,_) = Data.equal data Data.neutral

let get_concrete_data (d,_) = d

let mark (d,m) = d,Mark.mark m
let deallocate (d,_) = d,Mark.unknown
let unmark (d,m) = d,Mark.unmark m
let get_mark (_,v) = Mark.get_mark v

let set_data (data,m) d = (d,m)

let is_cleanable (d,m) = Data.is_cleanable d && Mark.is_cleanable m


(* type t = Data.t * Lock.t * Mark.t *)

(* let string_of (d,l,m) = sprintf "%s%s%s" (Data.string_of d) (if !enforce_no_cell_locking then "" else Lock.string_of l) (if !enforce_no_marking then "" else Mark.string_of m) *)

(* let to_dot (d,l,m) = sprintf "%s%s%s" (Data.string_of d) (if !enforce_no_cell_locking then "" else Lock.to_dot l) (if !enforce_no_marking then "" else Mark.to_dot m) *)

(* (\* let make d l m = d,l,m *\) *)

(* let unknown _ = Data.neutral,(if !enforce_no_cell_locking then Lock.default else Lock.default_unknown),(if !enforce_no_marking then Mark.default else Mark.unknown) *)

(* let default color = color,Lock.default,Mark.default *)

(* let compatible (data1,lock1,mark1) (data2,lock2,mark2) = *)
(*   Data.compatible data1 data2 && *)
(*   (if !enforce_no_cell_locking then true else Lock.compatible lock1 lock2) && *)
(*   (if !enforce_no_marking then true else Mark.compatible mark1 mark2) *)

(* let is_consistent pc ~cell_data:(data1,lock1,mark1) ~pattern_data:(data2,lock2,mark2) = *)
(*   Data.compatible data1 data2 && *)
(*   (if !enforce_no_cell_locking then true else Lock.are_consistent pc lock1 lock2) && *)
(*   (if !enforce_no_marking then true else Mark.compatible mark1 mark2) *)

(* let compare (d1,lock1,m1) (d2,lock2,m2) : int = *)
(*   let cv = Data.compare d1 d2 in *)
(*   if cv <> 0 then cv else begin *)
(*     match !enforce_no_cell_locking, !enforce_no_marking with *)
(*     | true,true -> 0 *)
(*     | true, false -> Mark.compare m1 m2 *)
(*     | false, true -> Lock.compare lock1 lock2 *)
(*     | false, false -> let cv2 = Lock.compare lock1 lock2 in if cv2 <> 0 then cv2 else Mark.compare m1 m2 *)
(*   end *)

(* let equal data1 data2 = compare data1 data2 = 0 *)

(* let meet (data1,lock1,m1) (data2,lock2,m2) = (Data.meet data1 data2), (if !enforce_no_cell_locking then Lock.default else Lock.meet lock1 lock2), (Mark.meet m1 m2) *)
(* let combine (data1,lock1,m1) (data2,lock2,m2) = (Data.meet data1 data2), (Lock.combine lock1 lock2), (Mark.meet m1 m2) *)
    
(* let join (data1,lock1,m1) (data2,lock2,m2) = (Data.join data1 data2), (Lock.join lock1 lock2), (Mark.join m1 m2) *)
      
(* let subsumes (data1,lock1,m1) (data2,lock2,m2) = *)
(*   Data.subsumes data1 data2 && *)
(*   (if !enforce_no_cell_locking then true else Lock.subsumes lock1 lock2) && *)
(*   (if !enforce_no_marking then true else Mark.subsumes m1 m2) *)

(* let is_neutral_data (data,_,_) = Data.equal data Data.neutral *)

(* let get_concrete_data (d,_,_) = d *)
    
(* let is_not_locked (_,l,_) = Lock.is_not_locked l *)
(* let is_locked_by who (_,l,_) = Lock.is_locked_by who l *)
(* let lock_by who (d,l,m) = d,(Lock.lock_by who l),m *)
(* let unlock (d,l,m) = d,(Lock.unlock l),m *)

(* let mark (d,l,m) = d,l,Mark.mark m *)
(* let unmark (d,l,m) = d,l,Mark.unmark m *)

(* let set_data (data,l,m) d = (d,l,m) *)

(* let is_cleanable (d,l,m) = Data.is_cleanable d && Lock.is_cleanable l && Mark.is_cleanable m *)

(* (\* let is_cleanable (d,l,m) = *\) *)
(* (\*   let res = Data.is_cleanable d && Lock.is_cleanable l && Mark.is_cleanable m in *\) *)
(* (\*   Debug.print "%s is cleanable (%B) because data:%B Lock:%B Mark:%B\n" (string_of (d,l,m)) res (Data.is_cleanable d) (Lock.is_cleanable l) (Mark.is_cleanable m); *\) *)
(* (\*   res *\) *)
