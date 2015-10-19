open Printf 

(* external get_time: unit -> int = "caml_get_time" *)
(* external delta_to_usec: int -> int = "caml_delta_to_usec" *)

let scount = ref 0
let tb = Buffer.create 20
let tab _ = Buffer.clear tb; for i=1 to !scount do Buffer.add_char tb '\t' done
(* let tab _ = let rec tab_rec (acc:string) (n:int) = if n>0 then tab_rec (acc^"\t") (n-1) else acc in tab_rec "" !scount *)
(* let level increment = () *)
let level increment = scount := !scount + increment

let print args = begin
   tab ();
   Buffer.output_buffer stdout tb;
   Printf.kfprintf flush stdout args
end

(* let print args = begin *)
(*   Format.fprintf *)
(*     Format.std_formatter *)
(*     "@[<hov %d>%t@]@?" *)
(*     !scount *)
(*     (fun _ -> Printf.printf args) *)
(* end *)

let pause message = begin
  print "\n=== Pausing (%s) === (press Enter to continue)" message;
  ignore(Pervasives.read_line ())
end

let red = "[7;31m"
let blue = "[7;36m"
let green = "[7;32m"
let fuschia = "[7;35m"
let yellow = "[7;33m"
let noColor = "[0m"
let eraseLine = "[2K\r"
let eraseScreen = "[2J"

let bold = "\033[1m"
let underline = "\033[4m"

let serialize thing name = begin
  let oc = open_out name in Printf.fprintf oc "%s" (Marshal.to_string thing []); close_out oc;
end
