
let progress = ref false
let results = ref false
let results_dir = ref "results"
let trace = ref false

let nullpointer_dereferencing = ref false
let danglingpointer = ref false
let free_dereferencing = ref false
let doublefree = ref false
let cycle = ref false

let get_options () : string = begin
  if !nullpointer_dereferencing || !danglingpointer || !free_dereferencing || !doublefree || !cycle
  then Printf.sprintf "with check for %s%s%s%s%s"
      (if !nullpointer_dereferencing then "null pointer dereferencing," else "")
      (if !danglingpointer then "dangling pointers," else "")
      (if !free_dereferencing then "free dereferencing," else "")
      (if !doublefree then "double-freeing," else "")
      (if !cycle then "cycles" else "")
  else "(Ignoring bad constraints, ie under-approximation)"
end

let print_progress size maxsize = begin
  assert( maxsize > 0 );
  assert( size <= maxsize );
  Printf.printf "[2K\r"; (* eraseLine *)
  let length = 50 in
  let limit = (size * length / maxsize) in
  for i=0 to limit do Printf.printf "*"; done;
  for i=limit+1 to length do Printf.printf "_"; done;
  Printf.printf "|";
end

(* Must be escaped *)
let mkdir name = ignore( Sys.command("mkdir -p "^name) )
