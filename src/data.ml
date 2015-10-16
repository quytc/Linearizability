
(* the data domain is a simple lattice: 
   -> top, written "*", denotes the set of all colors, 
   -> bottom, written _, denotes the empty set, 
   -> while the other elements denote singletons *)

type t = int * char

module S = Set.Make(struct type t = char let compare = Pervasives.compare end)

let count = ref (-1)

let mk str = incr count; !count,str
(*   match str with *)
(*   | "*" -> failwith("The * data is reserved. Please use another one"); *)
(*   | "_" -> failwith("The _ data is reserved. Please use another one"); *)
(*   | _ -> str *)
let reconstruct (i,str) = assert(i>=0); (i,str)

(* let bottom = -1, '_' *)
(* let neutral = -1, 'W' *)
(* let top = -1, '*' *)
(* let equal (x,xs) (y,ys) = (x=y) && (if x < 0 || y < 0 then xs=ys else true) *)

let bottom = -1, '_'
let neutral = -2, 'W'
let top = -3, '*'
let equal (x,xs) (y,ys) = (x=y) (* && (if x < 0 || y < 0 then xs=ys else true) *)

let compare (x,xs) (y,ys) =
  let c = Pervasives.compare x y in if c <> 0 then c else (if x < 0 || y < 0 then Pervasives.compare xs ys else 0)

let is_interesting d = not( equal neutral d || equal bottom d || equal top d )

let unpack (i,_) = i
let char_of (_,s) = s
let string_of (_,s) = Printf.sprintf "%c" s
let color = function
  | 'B' -> "#87CEFA" (* lightblue *)
  | 'R' -> "#B00000" (* lightred *)
  | '*' -> "green"
  | '_' -> "yellow"
  | _ -> "#D8D8D8" (* grey-ish *)

let buffer buf (_,s) = Buffer.add_char buf s

let meet d1 d2  = match d1, d2 with
| d1, d2 when (equal d1 d2) -> d1
| d1, d2 when (equal d1 top) -> d2
| d1, d2 when (equal d2 top) -> d1
| _ -> bottom
let compatible d1 d2 = not(equal bottom (meet d1 d2)) || (equal d1 bottom && equal d2 bottom)

let is_cleanable d = equal d neutral || equal d bottom
