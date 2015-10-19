type t = Global of int * string * int | Local of int * string * int 
type op = Push | Pop | Dequeue | Enqueue | Insert | Delete | CCAS
type r =  True | False | Undef | Success | Unsuccess


let global (i,str,j) = Global(i, String.uppercase str, j)
let local (i,str,j) = Local(i, String.lowercase str, j)

let is_global = function Global (_,_,_) -> true | Local (_,_,_) -> false 
let is_local = function Global (_,_,_) -> false | Local (_,_,_) -> true 
let is_elim_global =   function Global (_,_,i) -> if i = 2 then true else false | Local (_,_,_) -> false
let is_main_global =   function Global (_,_,i) -> if i = 1 then true else false | Local (_,_,_) -> false 
let is_lock_global =   function Global (_,_,i) -> if i = 3 then true else false | Local (_,_,_) -> false 
let is_new =   function Local (_,_,i) -> if i = 4 then true else false | Global (_,_,_) -> false    
let compare v1 v2 = match v1,v2 with
  | Global (a,_, _), Global (b,_,_) -> Pervasives.compare a b
  | Local (a,_,_), Local (b,_,_) -> Pervasives.compare a b
| _, _ -> 1
let equal v1 v2 = compare v1 v2 = 0
      
let hash = Hashtbl.hash

let unpack = function | Global (i,_,_) | Local (i,_,_) -> i
let string_of = function | Global (_,s,_) | Local (_,s,_) -> s
  


(** the label [null] represented by [#] *)
let nil = global (0,"#",1)

(** the label [bottom] represented by [_|_] *)
let bottom = global (1,"-",1)

(** the label [free] *)
let free = global (2,"!",1)

(** the label [locked] *)
let locked = global (3,"Locked",1)
