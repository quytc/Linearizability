let sprintf = Printf.sprintf
let debug = false
(* ========================================================================================================= *)
(* =====================                        Matrix                              ======================== *)
(* ========================================================================================================= *)

module ManySteps : Constraint.C = struct
let name = "Matrix - with many steps successor"

exception Found of int
exception Stop
    
(* Global counter, for identification *)  
let maxID = ref (-1)

(* ========================================================================== *)
type thread = {
    mutable var:int;
    mutable pc: int;
    mutable promise: Promise.t;
    mutable return: Data.t;
    (* mutable stack: Stack.t; *)
    mutable bits: bool array;
  }

let thread_create b = begin
  {pc=0;var=0;promise=Promise.NoPromise;return=Data.top;bits=(Array.make b false);(* stack=Stack.create 1; *) (* One argument in the stack *)}; 
end
    
let thread_to_dot th =
  sprintf "PC: %d     Promise: %s   Return: %s   Bits:[|%s]"
    th.pc (Promise.string_of th.promise) (Data.string_of th.return) (Array.fold_left (sprintf "%s%B|") "" th.bits)

let info_of_thread th =
  sprintf "%d-%s-%s-%s"
    th.pc (Promise.string_of th.promise) (Data.string_of th.return) (Array.fold_left (sprintf "%s,%B") "" th.bits)

let thread_compare th1 th2 = begin
  let c0 = Pervasives.compare th1.pc th2.pc in
  if c0 <> 0 then c0 else
  let c1 = Promise.compare th1.promise th2.promise in
  if c1 <> 0 then c1 else
  let c2 = Data.compare th1.return th2.return in
  if c2 <> 0 then c2 else
  let c3 = Pervasives.compare th1.var th2.var in
  if c3 <> 0 then c3 else begin
    let blength = Array.length th1.bits in
    assert( blength = Array.length th2.bits );
    let rec comp i = if i = blength then 0 else begin
      let c = Pervasives.compare th1.bits.(i) th2.bits.(i) in
      if c <> 0 then c else comp (i+1)
    end in comp 0
  end
end

(* ========================================================================== *)
type info = NoInfo | Reach | Equal (* | ReachStar *) (*  | Different | NoReach *) (* includes different *)
let string_of_info = function NoInfo -> "" (* "∅" *) | Reach -> "→" | Equal -> "=" (* | ReachStar -> "↣" *) (* | NoReach -> "↛" | Different -> "≠"  *)
    
(* ========================================================================== *)
type t = {

    mutable nth:int;
    mutable threads: thread array;
    mutable heap: info array array;
    mutable freecells: bool array;
    mutable bound: int;
    gvar: int;
    colors:int;

    mutable translation: string array;

    mutable observer: Observer.state;      (** The state of the observer *)

    mutable encoding: string;

    id:int;
    mutable messages:string list;
    mutable alive: bool;
    mutable parent: t option;
  } 
      
let create nth gvars gcolors b = incr maxID;
  let gvar = 2 + Array.length gvars in
  let colors = Array.length gcolors in
  let bound = gvar + colors in
  let h = Array.make_matrix bound bound NoInfo in
  for i=0 to bound - 1 do h.(i).(i) <- Equal; done;
  let freecells = Array.make bound false in
  {
  nth = nth;
  threads = Array.init nth (fun _ -> thread_create b);
  heap = h;
  freecells=freecells;
  gvar = gvar;
  colors = colors;
  bound = gvar + colors - 1;

  encoding=""; (* to be sanitized *)

  translation = Array.append
    (Array.map Label.string_of (Array.append [|Label.nil;Label.bottom|] gvars))
    (Array.map Data.string_of gcolors);

  id = (!maxID);
  messages = [];
  alive = true;
  observer = Observer.init;
  parent = None;
}

(* let start_globals p = 0 *)
(* let end_globals p = p.gvar - 1 *)
(* let start_colors p = p.gvar *)
(* let end_colors p = p.gvar + p.colors - 1 *)

let clone t = assert( t.alive ); incr maxID;
  { t with id=(!maxID);
    threads = Array.map (fun th -> {th with bits=Array.copy th.bits;}) t.threads;
    heap = Array.map Array.copy t.heap;
    freecells = Array.copy t.freecells;
    (* will copy the rest *) 
    (* and share the translations *)
    translation = Array.copy t.translation;
  }

let string_of t =
  sprintf "%s[Observer=%s%s]" (if t.alive then "" else "(deleted)")
    (Observer.string_of_state t.observer)
    (Array.fold_left (fun acc th -> sprintf "%s%s|" acc (info_of_thread th)) "|" t.threads)

(* ========================================================================================================= *)
(* =====================                        Printing                            ======================== *)
(* ========================================================================================================= *)

let to_html (p:t) (where:string) = begin
  
  let info = 
    sprintf "%s<p>ID: %d</p><p>Parent: %s</p><p>Encoding: %s</p><ol reversed>%s</ol>"
      (if p.alive then "" else "<p>Deleted</p>")
      p.id
      (match p.parent with None -> "orphelin" | Some papa -> string_of_int papa.id)
      p.encoding
      (List.fold_right (sprintf "<li>%s</li>%s") p.messages "")
  in

  let threads = ref "<div id=\"threads\">" in
  Array.iteri (fun thi th -> threads := sprintf "%s<p>Th %d: %s</p>" !threads thi (thread_to_dot th);) p.threads;
  threads := !threads ^ "</div>";

  let gbound = p.gvar + p.colors - 1 in

  let heap = ref "<table><thead><tr><th></th>" in
  for i=0 to gbound do
    heap := sprintf "%s<th>%s</th>" !heap p.translation.(i);
  done;
  let shift = ref (gbound + 1) in
  for t=0 to p.nth - 1 do
    for i = !shift to !shift + p.threads.(t).var - 1 do
      heap := sprintf "%s<th>%s<sub>%d</sub></th>" !heap p.translation.(i) t;
    done;
    shift := !shift + p.threads.(t).var;
  done;
  heap := !heap ^ "</tr></thead><tbody>";

  for i=0 to gbound do
    heap := sprintf "%s<tr><td class=\"name\">%s</td>" !heap p.translation.(i);
    for j=0 to p.bound do
      heap := sprintf "%s<td>%s</td>" !heap (string_of_info p.heap.(i).(j));
    done;
    heap := !heap ^ "</tr>";
  done;
  shift := gbound + 1;
  for t=0 to p.nth - 1 do
    for i = !shift to !shift + p.threads.(t).var - 1 do
      heap := sprintf "%s<tr><td class=\"name\">%s<sub>%d</sub></td>" !heap p.translation.(i) t;
      for j=0 to p.bound do
	heap := sprintf "%s<td>%s</td>" !heap (string_of_info p.heap.(i).(j));
      done;
      heap := !heap ^ "</tr>";
    done;
    shift := !shift + p.threads.(t).var;
  done;
  heap := !heap ^ "</tbody></table>";
  
  let freecells = ref "<table><thead><tr>" in
  for i=0 to gbound do
    freecells := sprintf "%s<th>%s</th>" !freecells p.translation.(i);
  done;
  shift := gbound + 1;
  for t=0 to p.nth - 1 do
    for i = !shift to !shift + p.threads.(t).var - 1 do
      freecells := sprintf "%s<th>%s<sub>%d</sub></th>" !freecells p.translation.(i) t;
    done;
    shift := !shift + p.threads.(t).var;
  done;
  freecells := !freecells ^ "</tr></thead><tbody><tr>";
  for i=0 to p.bound do
    freecells := sprintf "%s<td>%s</td>" !freecells (if p.freecells.(i) then "x" else "");
  done;
  freecells := !freecells ^ "</tr></tbody></table>";

  let css = "table{ border-collapse:collapse; margin:0 auto; } td { border: 1px solid black; padding:10px; text-align:center; min-width:30px; } th,table td.name {background:black; color:white; border: 1px solid white; padding:10px; text-align:center; min-width:30px; }" in

  let res = sprintf "<html><head><style>%s</style></head><body>%s<p>Observer: %s</p><hr/>%s<hr/>%s<hr/>%s</body></html>"
      css !threads (Observer.string_of_state p.observer) !heap !freecells info
  in
  let oc = open_out (where ^ ".html") in Printf.fprintf oc "%s" res; close_out oc;

end

let __t p i = begin
  let shift = ref (p.gvar + p.colors) in
  if i < !shift then p.translation.(i) else begin
    try for t=0 to p.nth - 1 do if i < !shift + p.threads.(t).var then raise (Found t) else shift := p.threads.(t).var + !shift; done; "unknown"
    with Found thi -> sprintf "%s.%d" p.translation.(i) thi
  end
end

module HT = Hashtbl.Make(struct type t = int let hash = Hashtbl.hash let equal = (=) end)
module S = Set.Make(struct type t = int * int let compare = Pervasives.compare end)
let to_dot (p:t) (where:string) = begin
  to_html p where;

  let generator = 
    let format s = (Str.global_substitute (Str.regexp "\n") (fun s -> "\\n") s) in
    fst (List.fold_right (fun s (acc,i) -> sprintf "--------------- %d ---------------\\n%s\\n%s" i (format s) acc, i+1) p.messages ("",1))
  in

  let threads = ref "subgraph threads {label=\"\";\n" in
  Array.iteri (fun thi th -> begin
    threads := sprintf "%sth%d [shape=box;label=\"Th:%d     %s\"];\n" !threads thi thi (thread_to_dot th);
  end) p.threads;
  threads := !threads ^ "}\n";

  let vertices = HT.create p.bound in
  let content = HT.create p.bound in
  let vcount = ref 0 in
  for i=0 to p.bound do 
    if not(HT.mem content i) then begin
      let all = ref [] in
      for j=0 to p.bound do if p.heap.(i).(j) = Equal then all := j :: !all; done;
      incr vcount;
      List.iter (fun j -> HT.add content j !vcount) !all;
      assert( List.length !all > 0 );
      HT.add vertices !vcount !all;
    end;
  done;

  let heap = ref "" in

  HT.iter (fun v indices -> begin
    assert( List.length indices > 0 );
    let colors = ref [] in
    let names = List.fold_left (fun acc i ->
      if p.gvar <= i && i < p.gvar + p.colors
      then ( colors := (__t p i) :: !colors; acc)
      else sprintf "%s%s," acc (__t p i)) "" indices
    in
    assert( List.length !colors < 2 );
    let fillcolor = Data.color (match !colors with [] -> "" | hd::_ -> hd) in

    let textcolor,allocation = if p.freecells.(List.hd indices) then "red"," | ✘" else "black","" in
    let text,shape =
      if List.mem (Label.unpack Label.nil) indices || List.mem (Label.unpack Label.bottom) indices
      then names, "ellipse"
      else sprintf "{%s%s}" names allocation, "Mrecord" in

    heap := sprintf "%sv_%d [label=\"%s\",shape=%s,style=filled,color=\"%s\",fillcolor=\"%s\"];\n" !heap v text shape textcolor fillcolor
  end) vertices;

  let edges = ref S.empty in
  for i=0 to p.bound do 
    for j=0 to p.bound do 
      if p.heap.(i).(j) = Reach then edges := S.add ((HT.find content i),(HT.find content j)) !edges;
    done;
  done;
  S.iter (fun (i,j) -> heap := sprintf "%sv_%d -> v_%d\n" !heap i j; ) !edges;

  let res = sprintf "digraph G {rankdir=LR;\nlabel=\"Observer: %s\\n%s\";\n%s\n%s\n}" (Observer.string_of_state p.observer) generator !threads !heap in
  let oc = open_out (where ^ ".dot") in Printf.fprintf oc "%s" res; close_out oc;
end

(* ========================================================================================================= *)
(* =====================                        Utilities                           ======================== *)
(* ========================================================================================================= *)
    
let id t = t.id
let observer t = t.observer
let set_observer t obs = t.observer <- obs
    
(*   let log t message = t.messages <- message::t.messages *)
let log t message = t.messages <- [message]

let nthreads p = p.nth

let is_alive t = t.alive
let delete t = t.alive <- false

let set_in_queue _ _ = ()
let in_queue _ = false
let set_in_slice _ _ = failwith("not implemented")
let in_slice _ = failwith("not implemented")

let set_parent p p' = p.parent <- Some p'
let parent p = match p.parent with None -> failwith("no parent") | Some papa -> papa

let pc p thi = p.threads.(thi).pc
let set_pc p thi pc = p.threads.(thi).pc <- pc  

let promise p thi = p.threads.(thi).promise
let set_promise p thi prom = p.threads.(thi).promise <- prom
let reset_promise p thi = set_promise p thi Promise.NoPromise

let _reset_thread th = begin
  th.var     <- 0;
  th.pc      <- 0;
  th.promise <- Promise.NoPromise;
  th.return  <- Data.top;
  for i=0 to Array.length th.bits - 1 do th.bits.(i) <- false done;
end

let rec iter_trace p f = begin
  f p;
  match p.parent with
  | Some papa when papa != p (*physically*) -> iter_trace papa f
  | _ -> ()
end

let print_trace p where = iter_trace p (fun p' -> to_dot p' (sprintf "%s-%d" where (id p')))

(* ========================================================================================================= *)
(* =====================                       Entailement                          ======================== *)
(* ========================================================================================================= *)

let hash p = Hashtbl.hash p.encoding

let compare p1 p2 = String.compare p1.encoding p2.encoding

let equal p1 p2 = p1.encoding = p2.encoding

(* =================================================================================== *)
let index p thi v = begin
  if Label.is_global v then Label.unpack v else begin
    let shift = ref 0 in
    for i = 0 to thi - 1 do shift := !shift + p.threads.(i).var done; (*shouldn't count when thi=0 *)
    p.gvar + p.colors + !shift + (Label.unpack v)
  end
end

(* =================================================================================== *)

exception NullPointerDereferencing of t * string
exception DoubleFree of t * string
exception Dangling of t * string
exception ClashWithInit of t

let check_dereferencing p thi i str = begin
  begin match p.heap.(i).(index p thi Label.nil) with
  | Equal (* | ReachStar *) -> raise (NullPointerDereferencing (p,str));
  | _ -> () end;
  begin match p.heap.(i).(index p thi Label.bottom) with
  | Equal (* | ReachStar *) -> raise (Dangling (p,str));
  | _ -> () end;
end

(* =================================================================================== *)

(* Return the labels that are placed on the succ cell, where i is placed. *)
(* It should be unik *)
let _succs p iv = begin
  assert( iv <> Label.unpack Label.nil && iv <> Label.unpack Label.bottom );
  let res = ref [] in
  for i=0 to p.bound do
    match p.heap.(iv).(i) with
    | Reach -> assert( i <> iv ); res := i :: !res;
    | _ -> ()
  done;
  match !res with
  | [] -> print_trace p "tmp/trace"; failwith(sprintf "I couldn't find the successor of %d" iv)
  | all ->
      assert(begin
	try List.iter (fun a -> List.iter (fun b -> if p.heap.(a).(b) <> Equal then raise Stop; ) all;) all; true
	with Stop ->
	  Debug.print "_succs: I found another thing that %d reaches" iv;
	  print_trace p "tmp/trace";
	  false
      end);
      all
end

let _preds p iv = begin
  let res = ref [] in
  for i=0 to p.bound do
    match p.heap.(i).(iv) with
    | Reach -> assert( i <> iv ); res := i :: !res;
    | _ -> ()
  done;
  !res
end
(* ========================================================================================================= *)
(* =====================                        Sanity check                        ======================== *)
(* ========================================================================================================= *)

exception Insane of t * string

let _check_sanity p = begin
  for i=0 to p.bound do
    for j=0 to p.bound do
      match p.heap.(i).(j) with
      |	Equal ->
	  if p.heap.(j).(i) <> Equal then raise (Insane (p,sprintf "Equality not matching %s,%s" (__t p i) (__t p j))); (* Transpose of Equality *)
	  if p.freecells.(i) <> p.freecells.(j) then raise (Insane (p,sprintf "Allocation %s,%s" (__t p i) (__t p j))); (* Allocation *)
	  for k=0 to p.bound do
	    if p.heap.(i).(k) = Equal && p.heap.(k).(j) <> Equal then raise (Insane (p,sprintf "Equal: %s,%s,%s" (__t p i) (__t p j) (__t p k))); (* Equality *)
	  done;
      |	Reach ->
	  for k=0 to p.bound do
	    if p.heap.(j).(k) = Equal && p.heap.(i).(k) <> Reach then raise (Insane (p,sprintf "Equal+Reach %s,%s,%s" (__t p i) (__t p j) (__t p k))); (* Equality + Reach *)
	    if p.heap.(i).(k) = Equal && p.heap.(k).(j) <> Reach then raise (Insane (p,sprintf "Equal+Reach %s,%s,%s" (__t p i) (__t p j) (__t p k))); (* Equality + Reach *)
	    if p.heap.(i).(k) = Reach && p.heap.(j).(k) <> Equal then raise (Insane (p,sprintf "Equal+Reach %s,%s,%s" (__t p i) (__t p j) (__t p k))); (* Equality + Reach *)
	  done;
      |	_ ->
	  for k=0 to p.bound do
	    if p.heap.(i).(k) = Equal && p.heap.(k).(j) = Equal then raise (Insane (p,sprintf "Equal: %s,%s,%s" (__t p i) (__t p j) (__t p k))); (* Equality *)
	  done;
    done;
  done;
end

let _in_global_world p iv = begin (* Color or Label *)
  let rec fetch i = begin
    if i < p.gvar then raise Stop;
    let preds = _preds p i in
    List.iter fetch preds;
  end in try fetch iv; false with Stop -> true
end


let _check_successors p = begin
  let iNil, iBottom = Label.unpack Label.nil, Label.unpack Label.bottom in
  for i=0 to p.bound do 
    if i >= p.gvar && i < p.gvar+p.colors && not(_in_global_world p i) then () else
    match p.heap.(i).(iNil), p.heap.(iBottom).(i) with
    | Equal,_ | _,Equal -> ()
    | _ -> 
	let succs = _succs p i in
	List.iter (fun a -> begin 
	  List.iter (fun b -> begin
	    match p.heap.(a).(b) with 
	    | Equal -> ()
	    | _ -> raise (Insane (p,sprintf "Different successors: %s,%s" (__t p a) (__t p a))); 
	  end) succs; 
	end) succs;
  done;
end

let _check_diagonal p = begin
  for i=0 to p.bound do match p.heap.(i).(i) with| Equal -> () | _ -> raise (Insane (p,sprintf "Wrong diagonal: %s" (__t p i))); done;
end

let is_sane (p:t) : bool = begin
  (* TO BE COMPLETED *)
  try
    _check_diagonal p;
    _check_sanity p;
    _check_successors p;
    true
  with Insane (c,str) -> Debug.print "%s %d is INSANE %s %s\n" Debug.red c.id Debug.noColor str; print_trace c "tmp/insane"; false
end

(* =================================================================================== *)

let sanitize p = begin
  assert( is_sane p );

  let string_of_freecell str fc = sprintf "%s%s" !str (if p.freecells.(fc) then "T" else "F") in
  let string_of_thread str th = sprintf "%s%s%d|" !str (info_of_thread th) th.var in
  let string_of_cell str i j = sprintf "%s%s|" !str (string_of_info p.heap.(i).(j)) in

  let info = sprintf "%s-%d-%d-%d-%d-" (Observer.string_of_state (observer p)) p.nth p.bound p.gvar p.colors in

  let threads1 = 
    let str = ref "" in
    for i=0 to p.nth - 1 do str := string_of_thread str p.threads.(i); done;
    !str
  in
  let allocation1 = 
    let str = ref "" in
    for i=0 to p.bound do str := string_of_freecell str i; done;
    !str
  in
  let shape1 = 
    let str = ref "" in
    for i=0 to p.bound do
      for j=0 to p.bound do str := string_of_cell str i j; done;
      str := !str ^ "|";
    done;
    !str
  in
  let encoding1 = sprintf "%s.%s.%s.%s." info threads1 shape1 allocation1 in

  if p.nth <> 2 then
    p.encoding <- encoding1
  else begin


  (* Trying to swap the 2 threads *)
    let threads2 =
      let str = ref "" in
      for i=p.nth - 1 downto 0 do str := string_of_thread str p.threads.(i); done;
      !str
    in
    let gbound = p.gvar + p.colors in
    let allocation2 =
      let str = ref "" in
      for i=0 to gbound - 1 do str := string_of_freecell str i; done;
      for i=gbound + p.threads.(0).var to p.bound do str := string_of_freecell str i; done;
      for i=gbound to gbound + p.threads.(0).var - 1 do str := string_of_freecell str i; done;
      !str
    in
    let shape2 =
      let str = ref "" in
      for i=0 to gbound - 1 do
	for j=0 to gbound - 1 do str := string_of_cell str i j; done;
	for j=gbound + p.threads.(0).var to p.bound do str := string_of_cell str i j; done;
	for j=gbound to gbound + p.threads.(0).var - 1 do str := string_of_cell str i j; done;
	str := !str ^ "|";
      done;
      for i=gbound + p.threads.(0).var to p.bound do
	for j=0 to gbound - 1 do str := string_of_cell str i j; done;
	for j=gbound + p.threads.(0).var to p.bound do str := string_of_cell str i j; done;
	for j=gbound to gbound + p.threads.(0).var - 1 do str := string_of_cell str i j; done;
	str := !str ^ "|";
      done;
      for i=gbound to gbound + p.threads.(0).var - 1 do
	for j=0 to gbound - 1 do str := string_of_cell str i j; done;
	for j=gbound + p.threads.(0).var to p.bound do str := string_of_cell str i j; done;
	for j=gbound to gbound + p.threads.(0).var - 1 do str := string_of_cell str i j; done;
	str := !str ^ "|";
      done;
      !str
    in
    let encoding2 = sprintf "%s.%s.%s.%s." info threads2 shape2 allocation2 in

  (* Keep the smallest version *)
    if String.compare encoding1 encoding2 < 0 then
      p.encoding <- encoding1
    else begin
      p.encoding <- encoding2;
      if debug then log p "symmetry swapping";
    end;

  end (* in case nth = 2 *)
end

  let post_process ?(sanitizing=true) p = begin
    if sanitizing then sanitize p;
    [p]
  end

(* =================================================================================== *)
let _remove_cell p iv = begin
  (* iv should be the only one that cell *)
  (* redirecting the edges *)
  let succs = _succs p iv in
  let preds = _preds p iv in
  List.iter (fun succ -> p.heap.(iv).(succ) <- NoInfo;) succs;
  List.iter (fun pred -> begin
    p.heap.(pred).(iv) <- NoInfo;
    List.iter (fun succ -> p.heap.(pred).(succ) <- Reach;) succs;
  end) preds;
end

let _kill_info p ix = begin
  for i=0 to p.bound do p.heap.(ix).(i) <- NoInfo; p.heap.(i).(ix) <- NoInfo; done;
  p.heap.(ix).(ix) <- Equal; (* Reset *)
  p.freecells.(ix) <- false;
end

let _remove_label p ix = begin
  (* If ix was with global variables or variables from other threads, do nothing *)
  try
    for i=0 to p.bound do match p.heap.(ix).(i) with | Equal when i <> ix -> raise Stop; | _ -> () done;
    (* ix was the last label on that cell *)
    _remove_cell p ix;
    _kill_info p ix;
  with Stop -> (* Leave that cell alone, just kill the info about ix *)
    _kill_info p ix;
end

(* Moving x to y *)
let _assign p ix iy = begin
  _remove_label p ix; (* that will remove the cell is ix was the last label on it, redirecting edges *)
  (* assigning it to iy now *)
  for i=0 to p.bound do
    p.heap.(ix).(i) <- p.heap.(iy).(i); (* Erase line, replace with iy *)
    p.heap.(i).(ix) <- p.heap.(i).(iy); (* Same with column *)
  done;
  p.heap.(ix).(ix) <- Equal;
  p.heap.(ix).(iy) <- Equal; (* Note: should not be needed here *)
  p.heap.(iy).(ix) <- Equal;

  p.freecells.(ix) <- p.freecells.(iy); (* allocation *)
end

let _remove_edge p src dst = begin
  for i=0 to p.bound do
    match p.heap.(src).(i) with
    | Equal -> (* Anything that is equal to src *)
	for j=0 to p.bound do
	  match p.heap.(dst).(j) with
	  | Equal -> (* Anything that is equal to dst *)
	      p.heap.(i).(j) <- NoInfo;
	  | _ -> ()
	done;
    | _ -> ()
  done;
end

let _add_edge p src dst = begin
  match p.heap.(src).(dst) with
  | Reach -> ()
  | Equal -> failwith("Eh? Cycle?")
  | _ -> begin
      for i=0 to p.bound do
	match p.heap.(src).(i) with
	| Equal -> (* Anything that is equal to src *)
	    for j=0 to p.bound do
	      match p.heap.(dst).(j) with
	      | Equal -> (* Anything that is equal to dst *)
		  p.heap.(i).(j) <- Reach;
	      | _ -> ()
	    done;
	| _ -> ()
      done;
  end
end

(* =================================================================================== *)
(* Must clone if necessary *)
let equality (x:Label.t) (y:Label.t) p thi : t list = begin
  let ix, iy = index p thi x, index p thi y in
  match p.heap.(ix).(iy) with
  | Equal -> [clone p]
  | _ -> []
end

(* Must clone if necessary *)
let non_equality (x:Label.t) (y:Label.t) p thi : t list = begin
  let ix, iy = index p thi x, index p thi y in
  match p.heap.(ix).(iy) with
  | Equal -> []
  | _ -> [clone p]
end

(* Must clone if necessary *)
let next_equality (x:Label.t) (y:Label.t) p thi : t list = begin
  (* x.next == y *)
  let ix,iy = index p thi x, index p thi y in
  check_dereferencing p thi ix (sprintf "%s.next == %s" (Label.string_of x) (Label.string_of y));
  match p.heap.(ix).(iy) with
  | Reach -> [clone p] (* cuz we assume precision *)
  | _ -> [] (* Either equal, not reached, or with more than one step *)
end

(* Must clone if necessary *)
let non_next_equality (x:Label.t) (y:Label.t) p thi = begin
  (* x.next =/= y *)
  let ix,iy = index p thi x, index p thi y in
  check_dereferencing p thi ix (sprintf "%s.next =/= %s" (Label.string_of x) (Label.string_of y));
  [clone p]
(*   match p.heap.(ix).(iy) with *)
(*   | Reach -> [] (\* cuz we assume precision *\) *)
(*   | _ -> [clone p] (\* Either equal, not reached, or with more than one step *\) *)
end

(* No need to clone *)
let set_return_value (p:t) (thi:int) (x:Label.t) : t list = begin
  (* ret := x.data *)
  let ix = index p thi x in
  check_dereferencing p thi ix (sprintf "ret := %s" (Label.string_of x));
  let color =
    try
      for ic = p.gvar to p.gvar + p.colors - 1 do
	match p.heap.(ix).(ic) with | Equal -> raise (Found ic) (* assuming precision *) | _ -> ()
      done;
      Data.neutral (* I didn't find anything equal... must be white *)
    with Found i -> (*just for data type*) Data.reconstruct (i - p.gvar, p.translation.(i))
  in
  p.threads.(thi).return <- color;
  [p]
end

(* No need to clone *)
  let reset_return_value (p:t) (thi:int) : t list = begin
  (* ret := star  *)
    p.threads.(thi).return <- Data.top;
    [p]
  end


(* No need to clone *)
let data_assign_var (p:t) (thi:int) (x:Label.t) (y:Label.t) : t list = begin
  failwith("Don't use it")
(*   (\* x.data := y *\) *)
(*   check_dereferencing p thi x; *)

(*   (\* CHEAT and MAKE IT STAR *\) *)
(*   [] *)
end

(* No need to clone *)
let assign (p:t) (thi:int) (x:Label.t) (y:Label.t) : t list = begin
  (* x := y *)
  let ix, iy = index p thi x, index p thi y in
  _assign p ix iy;
  [p]
end

let reset_counter p position = Array.iter (fun th -> if th.pc <> 0 then th.bits.(position) <- false;) p.threads
let is_uptodate p thi position = p.threads.(thi).bits.(position)
let make_uptodate p thi position = p.threads.(thi).bits.(position) <- true

(* No need to clone *)
let assign_dot_next (p:t) (thi:int) (x:Label.t) (y:Label.t) : t list = begin
  (* x := y.next *)

  (* Fetching the immediate successor *)
  let iy = index p thi y in
  check_dereferencing p thi iy (sprintf "%s := %s.next" (Label.string_of x) (Label.string_of y));
  let succs = _succs p iy in
  let ix = index p thi x in

  match succs with
  | [] -> failwith("can't be")
  | [isucc] when ix = isucc -> 
      [p]
  | isucc'::tail ->
      
      let isucc = if ix = isucc' then List.hd tail else isucc' in

      let p' = clone p in

      (* Placing x as isucc, the immediate successor of y *)
      if not(List.mem ix succs) then _assign p' ix isucc;

      (* Placing x in between y and isucc *)
      _remove_edge p iy isucc;
      _remove_label p ix;
      _add_edge p ix isucc;
      _add_edge p iy ix;
      p.freecells.(ix) <- false; (* I make x not deallocated anyway *)
      
      [p;p']
end

(* No need to clone *)
let dot_next_assign (p:t) (thi:int) (x:Label.t) (y:Label.t) : t list = begin
  (* x.next := y *)

  let ix,iy = index p thi x, index p thi y in
  check_dereferencing p thi ix (sprintf "%s.next := %s" (Label.string_of x) (Label.string_of y));
  assert( ix <> iy );

  let succs = _succs p ix in
  if not(List.mem iy succs) then begin
    _remove_edge p ix (List.hd succs);
    _add_edge p ix iy;
  end;
  [p]
  (* Nothing to do for the allocations *)
end

(* No need to clone *)
let make_new_cell (p:t) (thi:int) (x:Label.t) : t list = begin
  assert( Label.is_local x );
  assert( is_sane p );

  let ix = index p thi x in

  let res = ref [] in
  (* I inspect all free cells, I allocate them, and assign x to each *)
  for i=0 to p.bound do
    if p.freecells.(i) then begin
      let p' = clone p in
      for j=0 to p.bound do match p.heap.(i).(j) with | Equal -> p'.freecells.(j) <- false; | _ -> () done;
      _assign p' ix i;
      res := p' :: !res; (* it might create many same copies, but I don't care *)
    end;
  done;

    (* Last one: I add a new cell *)
  _remove_label p ix; (* p.freecells.(ix) <- false; *)
    (* Make it reach anything that iBottom is equal to *)
    (* No need to call _add_edge *)
  let iBottom = index p thi Label.bottom in
  for j=0 to p.bound do
    match p.heap.(iBottom).(j) with
    | Equal -> (* Anything that is equal to iBottom *)
	p.heap.(ix).(j) <- Reach;
    | _ -> ()
  done;

  p :: !res
end

(* No need to clone *)
let free_cell (p:t) (thi:int) (x:Label.t) : t list = begin

  let ix = index p thi x in
  check_dereferencing p thi ix (sprintf "free(%s)" (Label.string_of x));

  let iBottom = index p thi Label.bottom in
  let succs = _succs p ix in
  if not(List.mem iBottom succs) then begin
    _remove_edge p ix (List.hd succs);
    _add_edge p ix iBottom;
  end;

    (* Make the ones equal to ix free cells *)
  for i=0 to p.bound do match p.heap.(ix).(i) with | Equal -> p.freecells.(i) <- true; | _ -> () done;

  [p]
end

(* No need to clone *)
let init_thread p thi vars : t list = begin
  assert( p.threads.(thi).var = 0 );

  assert( try for i=0 to Array.length p.threads.(thi).bits - 1 do if p.threads.(thi).bits.(i) then raise Stop; done; true with Stop -> to_dot p "tmp/ouch"; false ); 

  let count = Array.length vars in
  let newBound = p.bound+count in
  let cut = begin
    let shift = ref 0 in
    for i=0 to p.nth - 1 do if i<thi then shift := p.threads.(i).var + !shift; done;
    p.gvar + p.colors + !shift
  end in
  
  let h = Array.make_matrix (newBound+1) (newBound+1) NoInfo in
  
  for i=0 to cut - 1 do
    for j=0 to cut - 1 do (* Copy the colors and globals *) h.(i).(j) <- p.heap.(i).(j); done;
    for j=cut to p.bound do (* Taking care of the threads *) h.(i).(j+count) <- p.heap.(i).(j); done;
  done;

  for i=cut to p.bound do
    for j=0 to cut - 1 do h.(i+count).(j) <- p.heap.(i).(j); done;
    for j=cut to p.bound do h.(i+count).(j+count) <- p.heap.(i).(j); done;
  done;

  (* assign them to bottom *)
  let iBottom = index p thi Label.bottom in
  for i=cut to cut + count - 1 do h.(iBottom).(i) <- Equal; done;
  for i=cut to cut + count - 1 do for j=0 to newBound do h.(i).(j) <- h.(iBottom).(j); done; done;
  for i=cut to cut + count - 1 do h.(i).(iBottom) <- Equal; done;
  for i=cut to cut + count - 1 do for j=0 to newBound do h.(j).(i) <- h.(j).(iBottom); done; done;

  let freecells = Array.make (newBound+1) false in
  for i=0 to cut - 1 do freecells.(i) <- p.freecells.(i); done;
  for i=cut to p.bound do freecells.(i+count) <- p.freecells.(i); done;
  (* between cut and cut+count-1, it's already false *)

  let trans = Array.make (newBound+1) "" in
  for i=0 to cut - 1 do trans.(i) <- p.translation.(i); done;
  for i=cut to p.bound do trans.(i+count) <- p.translation.(i); done;
  for i=0 to count - 1 do assert( i = Label.unpack vars.(i) ); trans.(cut+i) <- Label.string_of vars.(i); done;

  p.translation <- trans;
  p.bound <- newBound;
  p.heap <- h;
  p.freecells <- freecells;
  p.threads.(thi).var <- count;

  [p]
end

(* No need to clone *)
let kill_thread (p:t) (thi:int) : t list = begin

  let th = p.threads.(thi) in

  let newBound = p.bound - th.var in

  let h = Array.make_matrix (newBound+1) (newBound+1) NoInfo in

  let cut = begin
    let shift = ref 0 in
    for i=0 to p.nth - 1 do if i<thi then shift := p.threads.(i).var + !shift; done;
    p.gvar + p.colors + !shift
  end in

  (* Removing the thread labels, but also clean its vertices if necessary *)
  for i=cut to cut + th.var-1 do _remove_label p i; done;

  (* Copying to the new heap. AFTER the label removing!! *)
  for i=0 to cut - 1 do
    for j=0 to cut - 1 do h.(i).(j) <- p.heap.(i).(j); done;
    for j=cut to newBound do h.(i).(j) <- p.heap.(i).(j+th.var); done;
  done;
  for i=cut to newBound do
    for j=0 to cut - 1 do h.(i).(j) <- p.heap.(i+th.var).(j); done;
    for j=cut to newBound do h.(i).(j) <- p.heap.(i+th.var).(j+th.var); done;
  done;
  
  (* Work on freecells and colors *)
  let freecells = Array.make (newBound+1) false in
  for i=0 to cut - 1 do freecells.(i) <- p.freecells.(i); done;
  for i=cut to newBound do freecells.(i) <- p.freecells.(i+th.var); done;

  let trans = Array.make (newBound+1) "" in
  for i=0 to cut - 1 do trans.(i) <- p.translation.(i); done;
  for i=cut to newBound do trans.(i) <- p.translation.(i+th.var); done;

  p.bound <- newBound;
  p.heap <- h;
  p.translation <- trans;
  p.freecells <- freecells;
  _reset_thread p.threads.(thi);

  [p]
end

let concretize_data p thi v data = begin
  if Data.is_interesting data then begin
    let iv = index p thi v in
    let iData = p.gvar + Data.unpack data in
    (* assigning the color to iv *)
    for i=0 to p.bound do
      p.heap.(iData).(i) <- p.heap.(iv).(i); (* Erase line, replace with iy *)
      p.heap.(i).(iData) <- p.heap.(i).(iv); (* Same with column *)
    done;
    p.heap.(iData).(iData) <- Equal;
    p.heap.(iData).(iv) <- Equal; (* Note: should not be needed here *)
    p.heap.(iv).(iData) <- Equal;
    p.freecells.(iData) <- p.freecells.(iv); (* allocation *)
  end;
end

(* Must clone when needed *)
let validate_insert (porg:t) (thi:int) (var:Label.t) (all: (Observer.data * Observer.state) list ) : t list  = begin
  List.fold_left (fun acc (data_,s) -> match data_ with
  | Observer.NoData | Observer.State _ ->  failwith("that's a weird observer transition")
  | Observer.ObsData data -> begin
      match promise porg thi with
      | Promise.Insert dlist ->
	  List.fold_left (fun acc' d -> if Data.equal data d then begin
	    let p = clone porg in
	    set_observer p s;
	    concretize_data p thi var d;
	    reset_promise p thi;
	    p::acc
	  end else acc') acc dlist
      | _ -> acc (* wrong promise *)
  end) [] all
end

(* Must clone when needed *)
let validate_delete (porg:t) (thi:int) (all: (Observer.data * Observer.state) list ) : t list  = begin
  List.fold_left (fun acc (data,s) -> match data with
  | Observer.NoData | Observer.State _ ->  failwith("that's a weird observer transition")
  | Observer.ObsData d -> begin
      if Data.compatible porg.threads.(thi).return d then begin
	let p = clone porg in
	(* p.threads.(thi).return <- d; *)
	set_observer p s;
	reset_promise p thi;
	p::acc
      end else acc (* wrong promise *)
  end) [] all
end

(* Must clone when needed *)
let validate_empty (porg:t) (thi:int) (all: (Observer.data * Observer.state) list ) : t list  = begin
  List.fold_left (fun acc (data,s) -> match data with
  | Observer.ObsData _ | Observer.NoData ->  failwith("that's a weird observer transition")
  | Observer.State s' -> begin
      match promise porg thi with
      | Promise.ReturnEmpty obs when Observer.same_state obs s' ->
	  let p = clone porg in
	  set_observer p s;
	  reset_promise p thi;
	  p::acc
      | _ -> acc (* not the right promise: DIE !!! *)
  end) [] all
end


(* Must clone when needed *)
  let main_lock porg thi lock = failwith("not implemented")
  let main_unlock porg thi lock = failwith("not implemented")

(* (\* Must clone when needed *\) *)
(*   let main_lock porg thi lock = begin *)
(* (\*     assert( not(porg.lockstates.(lock).(thi)) ); (\\* we don't want to lock again *\\) *\) *)
(*     let locked = ref false in *)
(*     for t=0 to porg.nth - 1 do if porg.lockstates.(lock).(t) then locked := true; done; *)
(*     if !locked then [] else begin *)
(*       let p = clone porg in *)
(*       p.lockstates.(lock).(thi) <- true; *)
(*       [p] *)
(*     end *)
(*   end *)

(*   let main_unlock porg thi lock = begin *)
(*     assert( porg.lockstates.(lock).(thi) ); (\* we don't want to unlock a free lock *\) *)
(*     let p = clone porg in *)
(*     p.lockstates.(lock).(thi) <- false; *)
(*     [p] *)
(*   end *)

(* =================================================================================== *)

let create_queue nth (head:Label.t) (tail:Label.t) colors bits _ = begin

  assert( 2 = Label.unpack head && 3 = Label.unpack tail );
  let c = create nth [|head;tail|] colors bits in

  let iNull = index c (-1) Label.nil in
  let iHead = index c (-1) head in
  let iTail = index c (-1) tail in
  
  c.heap.(iHead).(iNull) <- Reach;
  c.heap.(iTail).(iNull) <- Reach;

  c.heap.(iHead).(iHead) <- Equal;
  c.heap.(iTail).(iTail) <- Equal;

  c.heap.(iHead).(iTail) <- Equal;
  c.heap.(iTail).(iHead) <- Equal;

  sanitize c;
  [c]
end

let create_stack nth (top:Label.t) colors bits _ = begin

  assert( 2 = Label.unpack top );
  let c = create nth [|top|] colors bits in

  let iNull = index c (-1) Label.nil in
  let iTop = index c (-1) top in
  
  c.heap.(iTop).(iNull) <- Equal;
  c.heap.(iNull).(iTop) <- Equal;
  c.heap.(iTop).(iTop) <- Equal;

  sanitize c;
  [c]
end

(* let create_empty_buckets _ _ = [] *)

let fake _ = begin
  let head = Label.global (2,"H") in
  let tail = Label.global (3,"T") in
  let h0 = Label.local (0,"h") in
  let t0 = Label.local (1,"t") in
  let next0 = Label.local (2,"next") in
  
  let h = Array.make_matrix 8 8 NoInfo in
  let freecells = Array.make 8 false in
  let c = {
    nth = 2;
    threads = Array.init 2 (fun _ -> thread_create 0);
    heap = h;
    freecells=freecells;
    gvar = 4;
    colors = 1;
    bound = 7;

    encoding=""; (* to be sanitized *)
    
    translation = [|Label.string_of Label.nil;Label.string_of Label.bottom;"H";"T";"R";"h";"t";"next";|];

    id = 0;
    messages = [];
    alive = true;
    observer = Observer.init;
    parent = None;
  } in

  let iNull = index c 0 Label.nil in
  let iHead = index c 0 head in
  let iTail = index c 0 tail in
  let ih0 = index c 0 h0 in
  let it0 = index c 0 t0 in
  let inext0 = index c 0 next0 in

  c.threads.(0).var <- 3;
  c.threads.(0).pc <- 110;
  c.threads.(0).return <- Data.neutral;
  
  h.(iHead).(iTail) <- Reach;
  h.(iHead).(it0) <- Reach;
  h.(iHead).(inext0) <- Reach;
  
  for i=0 to 7 do h.(i).(i) <- Equal; done;

  h.(iHead).(ih0) <- Equal;
  h.(ih0).(iHead) <- Equal;

  h.(ih0).(iTail) <- Reach;
  h.(ih0).(it0) <- Reach;
  h.(ih0).(inext0) <- Reach;

  h.(iHead).(iTail) <- Reach;
  h.(iHead).(it0) <- Reach;
  h.(iHead).(inext0) <- Reach;
  
  h.(iTail).(it0) <- Equal;
  h.(iTail).(inext0) <- Equal;
  h.(it0).(iTail) <- Equal;
  h.(it0).(inext0) <- Equal;
  h.(inext0).(iTail) <- Equal;
  h.(inext0).(it0) <- Equal;

  h.(iTail).(iNull) <- Reach;
  h.(it0).(iNull) <- Reach;
  h.(inext0).(iNull) <- Reach;

  sanitize c;
  c
end

type key = unit
let key _ = failwith("not implemented")
let string_of_key _ = failwith("not implemented")
let join_hash _ = failwith("not implemented")
let join_equal _ _ = failwith("not implemented")
let join ~org ~extra = failwith("not implemented")
let view _ _ = failwith("not implemented")
let build_key _ = failwith("not implemented")
let extend _ _ _ = failwith("not implemented")
let trim _ = failwith("not implemented")
let is_more_general _ _ = failwith("not implemented")

end (* end module ManySteps *)

(* ========================================================================================================= *)
(* =====================                        Matrix                              ======================== *)
(* ========================================================================================================= *)
module OneStep : Constraint.C = struct

  let name = "Matrix - with one step successor"

  exception Found of int
  exception Stop (* to break foldings and iterations *)
      
(* Global counter, for identification *)  
  let maxID = ref (-1)

(* ========================================================================== *)
  type thread = {
      mutable var:int;
      mutable pc: int;
      mutable promise: Promise.t;
      mutable return: Data.t;
    (* mutable stack: Stack.t; *)
      mutable bits: bool array;
    }

  let thread_create b = begin
    {pc=0;var=0;promise=Promise.NoPromise;return=Data.top;bits=(Array.make b false);(* stack=Stack.create 1; *) (* One argument in the stack *)}; 
  end
      
  let thread_to_dot th =
    sprintf "PC: %d     Promise: %s   Return: %s   Bits:[|%s]"
      th.pc (Promise.string_of th.promise) (Data.string_of th.return) (Array.fold_left (sprintf "%s%B|") "" th.bits)

  let info_of_thread th =
    sprintf "%d-%s-%s-%s"
      th.pc (Promise.string_of th.promise) (Data.string_of th.return) (Array.fold_left (sprintf "%s%B|") "Bits=|" th.bits)

  let thread_compare th1 th2 = begin
    let c0 = Pervasives.compare th1.pc th2.pc in
    if c0 <> 0 then c0 else
    let c1 = Promise.compare th1.promise th2.promise in
    if c1 <> 0 then c1 else
    let c2 = Data.compare th1.return th2.return in
    if c2 <> 0 then c2 else
    let c3 = Pervasives.compare th1.var th2.var in
    if c3 <> 0 then c3 else begin
      let blength = Array.length th1.bits in
      assert( blength = Array.length th2.bits );
      let rec comp i = if i = blength then 0 else begin
	let c = Pervasives.compare th1.bits.(i) th2.bits.(i) in
	if c <> 0 then c else comp (i+1)
      end in comp 0
    end
  end

(* ========================================================================== *)
  type info = NoInfo | Reach | Equal | OneStep
  let string_of_info = function NoInfo -> "" (* "∅" *) | Equal -> "=" | Reach -> "↣" | OneStep -> "→"

(* ========================================================================== *)
  type t = {

      mutable nth:int;
      mutable threads: thread array;
      mutable heap: info array array;
      mutable freecells: bool array;
      mutable bound: int;
      gvar: int;
      colors:int;
      lockstates: bool array array;
      locks: int;

      mutable translation: string array;

      mutable observer: Observer.state;      (** The state of the observer *)

      mutable encoding: string;

      id:int;
      mutable messages:string list;
      mutable alive: bool;
      mutable parent: t option;
    } 
	
  let create nth gvars gcolors b locks = incr maxID;
    let gvar = 2 + Array.length gvars in
    let colors = Array.length gcolors in
    let bound = gvar + colors in
    let h = Array.make_matrix bound bound NoInfo in
    for i=0 to bound - 1 do h.(i).(i) <- Equal; done;
    let freecells = Array.make bound false in
    {
    nth = nth;
    threads = Array.init nth (fun _ -> thread_create b);
    heap = h;
    freecells=freecells;
    gvar = gvar;
    colors = colors;
    bound = gvar + colors - 1;
    lockstates = (Array.make_matrix locks nth false);
    locks = locks - 1;

    encoding=""; (* to be sanitized *)

    translation = Array.append
      (Array.map Label.string_of (Array.append [|Label.nil;Label.bottom|] gvars))
      (Array.map Data.string_of gcolors);

    id = (!maxID);
    messages = [];
    alive = true;
    observer = Observer.init;
    parent = None;
  }

(*   let start_globals p = 0 *)
(*   let end_globals p = p.gvar - 1 *)
(*   let start_colors p = p.gvar *)
(*   let end_colors p = p.gvar + p.colors - 1 *)

  let clone t = assert( t.alive ); incr maxID;
    { t with id=(!maxID);
      threads = Array.map (fun th -> {th with bits=Array.copy th.bits;}) t.threads;
      heap = Array.map Array.copy t.heap;
      freecells = Array.copy t.freecells;
      lockstates = Array.map Array.copy t.lockstates;
    (* will copy the rest *) 
    (* and share the translations *)
      translation = Array.copy t.translation;
    }

  let string_of_locks p = begin
    let str = ref "" in
    for lock=0 to p.locks do
      for t=p.nth-1 downto 0 do
	str := sprintf "%s%s|" !str (if p.lockstates.(lock).(t) then "L" else "_");
      done;
      str := !str ^ "#";
    done;
    !str
  end

  let string_of t =
    sprintf "%s[Observer=%s,%s]" (if t.alive then "" else "(deleted)")
      (Observer.string_of_state t.observer)
      (Array.fold_left (fun acc th -> sprintf "%s%s|" acc (info_of_thread th)) "" t.threads)

(* ========================================================================================================= *)
(* =====================                        Printing                            ======================== *)
(* ========================================================================================================= *)

  let to_html (p:t) (where:string) = begin
    
    let info = 
      sprintf "%s<p>ID: %d</p><p>Parent: %s</p><p>Encoding: %s</p><ol reversed>%s</ol>"
	(if p.alive then "" else "<p>Deleted</p>")
	p.id
	(match p.parent with None -> "orphelin" | Some papa -> string_of_int papa.id)
	p.encoding
	(List.fold_right (sprintf "<li>%s</li>%s") p.messages "")
    in

    let threads = ref "<div id=\"threads\">" in
    Array.iteri (fun thi th -> threads := sprintf "%s<p>Th %d: %s</p>" !threads thi (thread_to_dot th);) p.threads;
    threads := !threads ^ "</div>";

    let gbound = p.gvar + p.colors - 1 in

    let heap = ref "<table><thead><tr><th></th>" in
    for i=0 to gbound do
      heap := sprintf "%s<th>%s</th>" !heap p.translation.(i);
    done;
    let shift = ref (gbound + 1) in
    for t=0 to p.nth - 1 do
      for i = !shift to !shift + p.threads.(t).var - 1 do
	heap := sprintf "%s<th>%s<sub>%d</sub></th>" !heap p.translation.(i) t;
      done;
      shift := !shift + p.threads.(t).var;
    done;
    heap := !heap ^ "</tr></thead><tbody>";

    for i=0 to gbound do
      heap := sprintf "%s<tr><td class=\"name\">%s</td>" !heap p.translation.(i);
      for j=0 to p.bound do
	heap := sprintf "%s<td>%s</td>" !heap (string_of_info p.heap.(i).(j));
      done;
      heap := !heap ^ "</tr>";
    done;
    shift := gbound + 1;
    for t=0 to p.nth - 1 do
      for i = !shift to !shift + p.threads.(t).var - 1 do
	heap := sprintf "%s<tr><td class=\"name\">%s<sub>%d</sub></td>" !heap p.translation.(i) t;
	for j=0 to p.bound do
	  heap := sprintf "%s<td>%s</td>" !heap (string_of_info p.heap.(i).(j));
	done;
	heap := !heap ^ "</tr>";
      done;
      shift := !shift + p.threads.(t).var;
    done;
    heap := !heap ^ "</tbody></table>";
    
    let freecells = ref "<table><thead><tr>" in
    for i=0 to gbound do
      freecells := sprintf "%s<th>%s</th>" !freecells p.translation.(i);
    done;
    shift := gbound + 1;
    for t=0 to p.nth - 1 do
      for i = !shift to !shift + p.threads.(t).var - 1 do
	freecells := sprintf "%s<th>%s<sub>%d</sub></th>" !freecells p.translation.(i) t;
      done;
      shift := !shift + p.threads.(t).var;
    done;
    freecells := !freecells ^ "</tr></thead><tbody><tr>";
    for i=0 to p.bound do
      freecells := sprintf "%s<td>%s</td>" !freecells (if p.freecells.(i) then "x" else "");
    done;
    freecells := !freecells ^ "</tr></tbody></table>";

    let locks = ref "<table><thead><tr><th></th>" in
    for t=0 to p.nth - 1 do
      locks := sprintf "%s<th>Th<sub>%d</sub></th>" !locks t;
    done;
    locks := !locks ^ "</tr></thead><tbody>";
    for i=0 to p.locks do
      locks := sprintf "%s<tr><td>Lock<sub>%d</sub></td>" !locks i;
      for t=0 to p.nth - 1 do
	locks := sprintf "%s<td>%s</td>" !locks (if p.lockstates.(i).(t) then "o" else "");
      done;
      locks := sprintf "%s</tr>" !locks;
    done;
    locks := !locks ^ "</tbody></table>";

    let css = "table{ border-collapse:collapse; margin:0 auto; } td { border: 1px solid black; padding:10px; text-align:center; min-width:30px; } th,table td.name {background:black; color:white; border: 1px solid white; padding:10px; text-align:center; min-width:30px; }" in

    let res = sprintf "<html><head><style>%s</style></head><body>%s<p>Encoding: %s</p><p>Observer: %s</p><hr/>%s<hr/>%s<hr/>%s<hr/>%s</body></html>"
	css !threads p.encoding (Observer.string_of_state p.observer) !heap !freecells !locks info
    in
    let oc = open_out (where ^ ".html") in Printf.fprintf oc "%s" res; close_out oc;

  end

  let __t p i = begin
    let shift = ref (p.gvar + p.colors) in
    if i < !shift then p.translation.(i) else begin
      try for t=0 to p.nth - 1 do if i < !shift + p.threads.(t).var then raise (Found t) else shift := p.threads.(t).var + !shift; done; "unknown"
      with Found thi -> sprintf "%s.%d" p.translation.(i) thi
    end
  end

  module HT = Hashtbl.Make(struct type t = int let hash = Hashtbl.hash let equal = (=) end)
  module S = Set.Make(struct type t = int * int * bool let compare = Pervasives.compare end)
  let to_dot (p:t) (where:string) = begin
    to_html p where;

    let generator = 
      let format s = (Str.global_substitute (Str.regexp "\n") (fun s -> "\\n") s) in
      fst (List.fold_right (fun s (acc,i) -> sprintf "--------------- %d ---------------\\n%s\\n%s" i (format s) acc, i+1) p.messages ("",1))
    in

    let threads = ref "subgraph threads {label=\"\";\n" in
    Array.iteri (fun thi th -> begin
      threads := sprintf "%sth%d [shape=box;label=\"Th:%d     %s\"];\n" !threads thi thi (thread_to_dot th);
    end) p.threads;
    threads := !threads ^ "}\n";

    let vertices = HT.create p.bound in
    let content = HT.create p.bound in
    let vcount = ref 0 in
    for i=0 to p.bound do 
      if not(HT.mem content i) then begin
	let all = ref [] in
	for j=0 to p.bound do if p.heap.(i).(j) = Equal then all := j :: !all; done;
	assert( List.length !all > 0 );
	incr vcount;
	List.iter (fun j -> HT.add content j !vcount) !all;
	HT.add vertices !vcount !all;
      end;
    done;

    let heap = ref "" in

    HT.iter (fun v indices -> begin
      assert( List.length indices > 0 );
      let colors = ref [] in
      let names = List.fold_left (fun acc i ->
	if p.gvar <= i && i < p.gvar + p.colors
	then begin colors := (__t p i) :: !colors; acc end 
	else sprintf "%s%s," acc (__t p i)) "" indices
      in
      assert( List.length !colors < 2 );
      let fillcolor = Data.color (match !colors with [] -> "" | hd::_ -> hd) in

      let textcolor,allocation = if p.freecells.(List.hd indices) then "red"," | ✘" else "black","" in
      let text,shape =
	if List.mem (Label.unpack Label.nil) indices || List.mem (Label.unpack Label.bottom) indices
	then names, "ellipse"
	else sprintf "{%s%s}" names allocation, "Mrecord" in

(*       let draw =  *)
(* 	match indices with *)
(* 	| [i] ->  *)
(* 	    if p.gvar <= i && i < p.gvar + p.colors then begin *)
(* 	      try for j=0 to p.bound do if p.heap.(i).(j) <> NoInfo || p.heap.(j).(i) <> NoInfo then raise Stop; done; false with Stop -> true *)
(* 	    end else true *)
(* 	| _ -> true *)
(*       in *)
(*       if draw then  *)
      heap := sprintf "%sv_%d [label=\"%s\",shape=%s,style=filled,color=\"%s\",fillcolor=\"%s\"];\n" !heap v text shape textcolor fillcolor;
    end) vertices;
    
    let edges = ref S.empty in
    for i=0 to p.bound do 
      for j=0 to p.bound do 
	match p.heap.(i).(j) with
	| OneStep -> edges := S.add ((HT.find content i),(HT.find content j),true) !edges;
	| Reach -> edges := S.add ((HT.find content i),(HT.find content j),false) !edges;
	| _ -> ()
      done;
    done;
    S.iter (fun (i,j,onestep) -> heap := sprintf "%sv_%d -> v_%d %s\n" !heap i j (if onestep then "" else "[style=dashed]"); ) !edges;

    let res =
      sprintf "digraph G {rankdir=LR;\nlabel=\"Observer: %s\\n%s%s\";\n%s\n%s\n}"
	(Observer.string_of_state p.observer) (if debug then sprintf "Encoding: %s\\n" p.encoding else "") generator !threads !heap
    in
    let oc = open_out (where ^ ".dot") in Printf.fprintf oc "%s" res; close_out oc;
  end

(* ========================================================================================================= *)
(* =====================                        Utilities                           ======================== *)
(* ========================================================================================================= *)
      
  let id t = t.id
  let observer t = t.observer
  let set_observer t obs = t.observer <- obs
      
(*   let log t message = t.messages <- message::t.messages *)
  let log t message = t.messages <- [message]

  let nthreads p = p.nth

  let is_alive t = t.alive
  let delete t = t.alive <- false

  let set_in_queue _ _ = ()
  let in_queue _ = false
  let set_in_slice _ _ = failwith("not implemented")
  let in_slice _ = failwith("not implemented")

  let set_parent p p' = p.parent <- Some p'
  let parent p = match p.parent with None -> failwith("no parent") | Some papa -> papa

  let pc p thi = p.threads.(thi).pc
  let set_pc p thi pc = p.threads.(thi).pc <- pc  

  let promise p thi = p.threads.(thi).promise
  let set_promise p thi prom = p.threads.(thi).promise <- prom
  let reset_promise p thi = set_promise p thi Promise.NoPromise

  let _reset_thread th = begin
    th.var     <- 0;
    th.pc      <- 0;
    th.promise <- Promise.NoPromise;
    th.return  <- Data.top;
    for i=0 to Array.length th.bits - 1 do th.bits.(i) <- false done;
  end

  let rec iter_trace p f = begin
    f p;
    match p.parent with
    | Some papa when papa != p (*physically*) -> iter_trace papa f
    | _ -> ()
  end

  let print_trace p where = iter_trace p (fun p' -> to_dot p' (sprintf "%s-%d" where (id p')))

(* ========================================================================================================= *)
(* =====================                       Entailement                          ======================== *)
(* ========================================================================================================= *)

  let hash p = Hashtbl.hash p.encoding
  let equal p1 p2 = p1.encoding = p2.encoding

(* =================================================================================== *)
  let index p thi v = begin
    if Label.is_global v then Label.unpack v else begin
      let shift = ref 0 in
      for i = 0 to thi - 1 do shift := !shift + p.threads.(i).var done; (*shouldn't count when thi=0 *)
      p.gvar + p.colors + !shift + (Label.unpack v)
    end
  end

(* =================================================================================== *)

  exception NullPointerDereferencing of t * string
  exception DoubleFree of t * string
  exception Dangling of t * string
  exception ClashWithInit of t

  let check_dereferencing p thi i str = begin
    begin match p.heap.(i).(index p thi Label.nil) with
    | Equal -> raise (NullPointerDereferencing (p,str));
    | _ -> () end;
    begin match p.heap.(i).(index p thi Label.bottom) with
    | Equal -> raise (Dangling (p,str));
    | _ -> () end;
  end

(* =================================================================================== *)

  type key = string
  let key p = p.encoding
  let string_of_key k = k
  let join_hash k = Hashtbl.hash k
  let join_equal = (=)

  let join_info org extra = begin
    match org,extra with
    | OneStep, Reach -> Some Reach
    | OneStep, OneStep
    | Reach, OneStep
    | Reach, Reach -> None
    | a,b when a <> b -> raise Stop
    | _ -> None
  end

  let join ~org ~extra : bool = begin
    let changed = ref false in
    for i=0 to org.bound do
      for j=0 to org.bound do
	try 
	  match join_info org.heap.(i).(j) extra.heap.(i).(j) with
	  | Some info -> org.heap.(i).(j) <- info; changed := true;
	  | None -> ()
	with Stop ->
	  Debug.print "Eh? Joining (%d,%d) %s and %s\n" i j (string_of_info org.heap.(i).(j)) (string_of_info extra.heap.(i).(j));
	  print_trace org "tmp/_debug/join";
	  to_dot org "tmp/_join-org";
	  to_dot extra "tmp/_join-extra";
	  failwith("Impossible")
      done;
    done;
    !changed
  end

(* =================================================================================== *)

(* Return the labels that are placed on the succ cell, where i is placed. *)
(* It should be unik *)
  let _succs p iv = begin
    assert( iv <> Label.unpack Label.nil && iv <> Label.unpack Label.bottom );
    let resOneStep = ref [] in
    let resReach = ref [] in
    for i=0 to p.bound do
      match p.heap.(iv).(i) with
      | Reach -> assert( i <> iv ); resReach := i :: !resReach;
      | OneStep -> assert( i <> iv ); resOneStep := i :: !resOneStep;
      | _ -> ()
    done;
    match !resReach, ! resOneStep with
    | [],[] -> print_trace p "tmp/trace"; failwith(sprintf "I couldn't find the successor of %d" iv)
    | all,[] | [], all ->
	assert(begin
	  try List.iter (fun a -> List.iter (fun b -> if p.heap.(a).(b) <> Equal then raise Stop; ) all;) all; true
	  with Stop ->
	    Debug.print "_succs: I found another thing that %d reaches" iv;
	    print_trace p "tmp/trace";
	    false
	end);
	all
    | _,_ ->  print_trace p "tmp/trace"; failwith(sprintf "Inconsistent successors of %d" iv)
  end

  let _preds p iv = begin
    let res = ref [] in
    for i=0 to p.bound do
      match p.heap.(i).(iv) with
      | Reach | OneStep -> assert( i <> iv ); res := i :: !res;
      | _ -> ()
    done;
    !res
  end
(* ========================================================================================================= *)
(* =====================                        Sanity check                        ======================== *)
(* ========================================================================================================= *)

  exception Insane of t * string

  let _check_sanity p = begin
    for i=0 to p.bound do
      for j=0 to p.bound do
	match p.heap.(i).(j) with
	| Equal ->
	    if p.heap.(j).(i) <> Equal then raise (Insane (p,sprintf "Equality not matching %s,%s" (__t p i) (__t p j))); (* Transpose of Equality *)
	    if p.freecells.(i) <> p.freecells.(j) then raise (Insane (p,sprintf "Allocation %s,%s" (__t p i) (__t p j))); (* Allocation *)
	    for k=0 to p.bound do
	      if p.heap.(i).(k) = Equal && p.heap.(k).(j) <> Equal then raise (Insane (p,sprintf "Equal: %s,%s,%s" (__t p i) (__t p j) (__t p k)));
	    done;
	| Reach ->
	    for k=0 to p.bound do
	      if p.heap.(j).(k) = Equal && p.heap.(i).(k) <> Reach then raise (Insane (p,sprintf "Equal+Reach %s,%s,%s" (__t p i) (__t p j) (__t p k)));
	      if p.heap.(i).(k) = Equal && p.heap.(k).(j) <> Reach then raise (Insane (p,sprintf "Equal+Reach %s,%s,%s" (__t p i) (__t p j) (__t p k)));
	      if p.heap.(i).(k) = Reach && p.heap.(j).(k) <> Equal then raise (Insane (p,sprintf "Equal+Reach %s,%s,%s" (__t p i) (__t p j) (__t p k)));
	    done;
	| OneStep ->
	    for k=0 to p.bound do
	      if p.heap.(j).(k) = Equal && p.heap.(i).(k) <> OneStep then raise (Insane (p,sprintf "Equal+OneStepReach %s,%s,%s" (__t p i) (__t p j) (__t p k)));
	      if p.heap.(i).(k) = Equal && p.heap.(k).(j) <> OneStep then raise (Insane (p,sprintf "Equal+OneStepReach %s,%s,%s" (__t p i) (__t p j) (__t p k)));
	      if p.heap.(i).(k) = OneStep && p.heap.(j).(k) <> Equal then raise (Insane (p,sprintf "Equal+OneStepReach %s,%s,%s" (__t p i) (__t p j) (__t p k)));
	    done;
	| _ -> ()
      done;
    done;
  end

  let _in_global_world p iv = begin (* Color or Label *)
    let rec fetch i = begin
      if i < p.gvar then raise Stop;
      let preds = _preds p i in
      List.iter fetch preds;
    end in try fetch iv; false with Stop -> true
  end


  let _check_successors p = begin
    let iNil, iBottom = Label.unpack Label.nil, Label.unpack Label.bottom in
    for i=0 to p.bound do 
      if i >= p.gvar && i < p.gvar+p.colors && not(_in_global_world p i) then () else
      match p.heap.(i).(iNil), p.heap.(iBottom).(i) with
      | Equal,_ | _,Equal -> ()
      | _ -> 
	  let succs = _succs p i in
	  List.iter (fun a -> begin 
	    List.iter (fun b -> begin
	      match p.heap.(a).(b) with 
	      | Equal -> ()
	      | _ -> raise (Insane (p,sprintf "Different successors: %s,%s" (__t p a) (__t p a))); 
	    end) succs; 
	  end) succs;
    done;
  end

  let _check_diagonal p = begin
    for i=0 to p.bound do match p.heap.(i).(i) with| Equal -> () | _ -> raise (Insane (p,sprintf "Wrong diagonal: %s" (__t p i))); done;
  end

  let is_sane (p:t) : bool = begin
  (* TO BE COMPLETED *)
    try
      _check_diagonal p;
      _check_sanity p;
      _check_successors p;
      true
    with Insane (c,str) -> Debug.print "%s %d is INSANE %s %s\n" Debug.red c.id Debug.noColor str; print_trace c "tmp/insane"; false
  end

(* =================================================================================== *)

  let sanitize p = begin
    assert( is_sane p );

    let string_of_freecell str fc = sprintf "%s%s" !str (if p.freecells.(fc) then "T" else "F") in
    let string_of_thread str th = sprintf "%s%s%d|" !str (info_of_thread th) th.var in
    (* I encode the OneStep as the Reach, so that we join similar matrices, we almost the same shape *)
    (* It has the advantage the joined matrices will keep the same hash *)
    let string_of_cell str i j = sprintf "%s%s|" !str (string_of_info (match p.heap.(i).(j) with | OneStep -> Reach | i -> i)) in
    let string_of_lock str lock t = sprintf "%s%s|" !str (if p.lockstates.(lock).(t) then "L" else "_") in
    let encode = sprintf "%s.%s.%s.%s.%s." in


    let info = sprintf "%s-%d-%d-%d-%d-" (Observer.string_of_state (observer p)) p.nth p.bound p.gvar p.colors in

    let threads1 = 
      let str = ref "" in
      for i=0 to p.nth - 1 do str := string_of_thread str p.threads.(i); done;
      !str
    in
    let allocation1 = 
      let str = ref "" in
      for i=0 to p.bound do str := string_of_freecell str i; done;
      !str
    in
    let shape1 = 
      let str = ref "" in
      for i=0 to p.bound do
	for j=0 to p.bound do str := string_of_cell str i j; done;
	str := !str ^ "|";
      done;
      !str
    in
    let locks1 = 
      let str = ref "" in
      for lock=0 to p.locks do for t=0 to p.nth-1 do str := string_of_lock str lock t; done; str := !str ^ "#"; done;
      !str
    in
    let encoding1 = encode info threads1 shape1 allocation1 locks1 in

    if p.nth <> 2 then
      p.encoding <- encoding1
    else begin

      (* Trying to swap the 2 threads *)
      let threads2 =
	let str = ref "" in
	str := string_of_thread str p.threads.(1);
	str := string_of_thread str p.threads.(0);
	!str
      in
      let gbound = p.gvar + p.colors in
      let allocation2 =
	let str = ref "" in
	for i=0 to gbound - 1 do str := string_of_freecell str i; done;
	for i=gbound + p.threads.(0).var to p.bound do str := string_of_freecell str i; done;
	for i=gbound to gbound + p.threads.(0).var - 1 do str := string_of_freecell str i; done;
	!str
      in
      let shape2 =
	let str = ref "" in
	for i=0 to gbound - 1 do
	  for j=0 to gbound - 1 do str := string_of_cell str i j; done;
	  for j=gbound + p.threads.(0).var to p.bound do str := string_of_cell str i j; done;
	  for j=gbound to gbound + p.threads.(0).var - 1 do str := string_of_cell str i j; done;
	  str := !str ^ "|";
	done;
	for i=gbound + p.threads.(0).var to p.bound do
	  for j=0 to gbound - 1 do str := string_of_cell str i j; done;
	  for j=gbound + p.threads.(0).var to p.bound do str := string_of_cell str i j; done;
	  for j=gbound to gbound + p.threads.(0).var - 1 do str := string_of_cell str i j; done;
	  str := !str ^ "|";
	done;
	for i=gbound to gbound + p.threads.(0).var - 1 do
	  for j=0 to gbound - 1 do str := string_of_cell str i j; done;
	  for j=gbound + p.threads.(0).var to p.bound do str := string_of_cell str i j; done;
	  for j=gbound to gbound + p.threads.(0).var - 1 do str := string_of_cell str i j; done;
	  str := !str ^ "|";
	done;
	!str
      in
      let locks2 = 
	let str = ref "" in
	for lock=0 to p.locks do for t=p.nth-1 downto 0 do str := string_of_lock str lock t; done; str := !str ^ "#"; done;
	!str
      in
      let encoding2 = encode info threads2 shape2 allocation2 locks2 in
      
      (* Keep the smallest version *)
      if String.compare encoding1 encoding2 < 0 then
	p.encoding <- encoding1
      else begin
	p.encoding <- encoding2;
	if debug then log p "symmetry swapping";

	(* Must swap the matrices *)

	let th0 = p.threads.(0) in
	let th1 = p.threads.(1) in
	p.threads.(0) <- th1;
	p.threads.(1) <- th0;

	let gbound = p.gvar + p.colors in
	let items = ref [] in
	for i=gbound to gbound + th0.var - 1 do items := p.freecells.(i) :: !items; done; (* Remember the old thread1 *)
	(* Move thread2 and erase thread one *)
	for i=gbound + th0.var to p.bound do p.freecells.(i-th0.var) <- p.freecells.(i); done;
	(* Copy back the items *)
	let position = ref p.bound in
	List.iter (fun item -> p.freecells.(!position) <- item; decr position;) !items;

	let items' = ref [] in
	for i=gbound to gbound + th0.var - 1 do items' := p.translation.(i) :: !items'; done; (* Remember the old thread1 *)
	(* Move thread2 and erase thread one *)
	for i=gbound + th0.var to p.bound do p.translation.(i-th0.var) <- p.translation.(i); done;
	(* Copy back the items *)
	position := p.bound;
	List.iter (fun item -> p.translation.(!position) <- item; decr position;) !items';

	let h = Array.make_matrix (p.bound+1) (p.bound+1) NoInfo in

	for i=0 to gbound - 1 do
	  for j=0 to gbound - 1 do h.(i).(j) <- p.heap.(i).(j) done;
	  for j=gbound to gbound + th0.var - 1 do h.(i).(j+th1.var) <- p.heap.(i).(j) done;
	  for j=gbound + th0.var to p.bound do h.(i).(j-th0.var) <- p.heap.(i).(j) done;
	done;
	for i=gbound + th0.var to p.bound do
	  for j=0 to gbound - 1 do h.(i-th0.var).(j) <- p.heap.(i).(j) done;
	  for j=gbound + th0.var to p.bound do h.(i-th0.var).(j-th0.var) <- p.heap.(i).(j) done;
	  for j=gbound to gbound + th0.var - 1 do h.(i-th0.var).(j+th1.var) <- p.heap.(i).(j) done;
	done;
	for i=gbound to gbound + th0.var - 1 do
	  for j=0 to gbound - 1 do h.(i+th1.var).(j) <- p.heap.(i).(j) done;
	  for j=gbound + th0.var to p.bound do h.(i+th1.var).(j-th0.var) <- p.heap.(i).(j) done;
	  for j=gbound to gbound + th0.var - 1 do h.(i+th1.var).(j+th1.var) <- p.heap.(i).(j) done;
	done;

	p.heap <- h;

	for lock=0 to p.locks do
	  let tmp = p.lockstates.(lock).(0) in
	  p.lockstates.(lock).(0) <- p.lockstates.(lock).(1);
	  p.lockstates.(lock).(1) <- tmp;
	done;

	assert(begin
	  let threads2' = ref "" in
	  threads2' := string_of_thread threads2' p.threads.(0);
	  threads2' := string_of_thread threads2' p.threads.(1);
	  let allocation2' = ref "" in for i=0 to p.bound do allocation2' := string_of_freecell allocation2' i; done;
	  let shape2' = ref "" in for i=0 to p.bound do for j=0 to p.bound do shape2' := string_of_cell shape2' i j; done; shape2' := !shape2' ^ "|"; done;
	  let locks2' = ref "" in for lock=0 to p.locks do for t=0 to p.nth-1 do locks2' := string_of_lock locks2' lock t; done; locks2' := !locks2' ^ "#"; done;
	  let encoding2' = encode info !threads2' !shape2' !allocation2' !locks2' in
(* 	  encoding2 = encoding2' *)
	  if encoding2 = encoding2' then true else begin
	    Debug.print "p.bound: %d\n" p.bound;
	    Debug.print "gbound : %d\n" gbound;
	    Debug.print "th0.var: %d\n" th0.var;
	    Debug.print "th1.var: %d\n" th1.var;
	    Debug.print "Encoding : %s\n" encoding2;
	    Debug.print "Encoding': %s\n" encoding2';
	    to_dot p "tmp/_after";
	    false
	  end
	end);
      
      end;

    end (* in case nth = 2 *)
  end

  let post_process ?(sanitizing=true) p = begin
    if sanitizing then sanitize p;
    [p]
  end

(* =================================================================================== *)
  let _remove_cell p iv = begin
  (* iv should be the only one that cell *)
  (* redirecting the edges *)
    let succs = _succs p iv in
    let preds = _preds p iv in
    List.iter (fun succ -> p.heap.(iv).(succ) <- NoInfo;) succs;
    List.iter (fun pred -> begin
      p.heap.(pred).(iv) <- NoInfo;
      List.iter (fun succ -> p.heap.(pred).(succ) <- Reach;) succs; (* That makes them many steps away *)
    end) preds;
  end

  let _kill_info p ix = begin
    for i=0 to p.bound do p.heap.(ix).(i) <- NoInfo; p.heap.(i).(ix) <- NoInfo; done;
    p.heap.(ix).(ix) <- Equal; (* Reset *)
    p.freecells.(ix) <- false;
  end

  let _remove_label p ix = begin
  (* If ix was with global variables or variables from other threads, do nothing *)
    try
      for i=0 to p.bound do match p.heap.(ix).(i) with | Equal when i <> ix -> raise Stop; | _ -> () done;
    (* ix was the last label on that cell *)
      _remove_cell p ix;
      _kill_info p ix;
    with Stop -> (* Leave that cell alone, just kill the info about ix *)
      _kill_info p ix;
  end

(* Moving x to y *)
  let _assign p ix iy = begin
    _remove_label p ix; (* that will remove the cell is ix was the last label on it, redirecting edges *)
  (* assigning it to iy now *)
    for i=0 to p.bound do
      p.heap.(ix).(i) <- p.heap.(iy).(i); (* Erase line, replace with iy *)
      p.heap.(i).(ix) <- p.heap.(i).(iy); (* Same with column *)
    done;
    p.heap.(ix).(ix) <- Equal;
    p.heap.(ix).(iy) <- Equal; (* Note: should not be needed here *)
    p.heap.(iy).(ix) <- Equal;

    p.freecells.(ix) <- p.freecells.(iy); (* allocation *)
  end

  let _remove_edge p src dst = begin
    for i=0 to p.bound do
      match p.heap.(src).(i) with
      | Equal -> (* Anything that is equal to src *)
	  for j=0 to p.bound do
	    match p.heap.(dst).(j) with
	    | Equal -> (* Anything that is equal to dst *)
		p.heap.(i).(j) <- NoInfo;
	    | _ -> ()
	  done;
      | _ -> ()
    done;
  end

  let _add_edge p src dst etype = begin
    match p.heap.(src).(dst) with
    | e when e = etype -> ()
    | Equal -> failwith("Eh? Cycle?")
    | _ -> begin
	for i=0 to p.bound do
	  match p.heap.(src).(i) with
	  | Equal -> (* Anything that is equal to src *)
	      for j=0 to p.bound do
		match p.heap.(dst).(j) with
		| Equal -> (* Anything that is equal to dst *)
		    p.heap.(i).(j) <- etype;
		| _ -> ()
	      done;
	  | _ -> ()
	done;
    end
  end

(* =================================================================================== *)
  let reset_counter p position = Array.iter (fun th -> if th.pc <> 0 then th.bits.(position) <- false;) p.threads
  let is_uptodate p thi position = p.threads.(thi).bits.(position)
  let make_uptodate p thi position = p.threads.(thi).bits.(position) <- true

(* Must clone if necessary *)
  let equality (x:Label.t) (y:Label.t) p thi : t list = begin
    let ix, iy = index p thi x, index p thi y in
    match p.heap.(ix).(iy) with
    | Equal -> [clone p]
    | _ -> []
  end

(* Must clone if necessary *)
  let non_equality (x:Label.t) (y:Label.t) p thi : t list = begin
    let ix, iy = index p thi x, index p thi y in
    match p.heap.(ix).(iy) with
    | Equal -> []
    | _ -> [clone p]
  end

(* Must clone if necessary *)
  let next_equality (x:Label.t) (y:Label.t) p thi : t list = begin
    (* x.next == y *)
    (* QUESTION: what to do if x.next is bottom. *)
    let ix,iy = index p thi x, index p thi y in
    check_dereferencing p thi ix (sprintf "%s.next == %s" (Label.string_of x) (Label.string_of y));
    match p.heap.(ix).(iy) with
    | OneStep -> [clone p] (* cuz we assume precision *)
    | Reach -> begin	
	let p' = clone p in
	_remove_edge p' ix iy; (* Reset the edge to be a one-step edge! *)
	_add_edge p' ix iy OneStep;
	[p']
    end
    | _ -> begin
	match p.heap.(ix).(index p thi Label.bottom) with
	| OneStep -> failwith("x.next == bottom") (* It means x.next can be any value, so in particular y... *)
	| Reach -> failwith("x.next == bottom")
	| _ -> []
    end
 
  end

(* Must clone if necessary *)
  let non_next_equality (x:Label.t) (y:Label.t) p thi = begin
    (* x.next =/= y *)
    let ix,iy = index p thi x, index p thi y in
    check_dereferencing p thi ix (sprintf "%s.next =/= %s" (Label.string_of x) (Label.string_of y));
    match p.heap.(ix).(iy) with
    | OneStep -> []
    | _ -> [clone p]
  end

(* No need to clone *)
  let set_return_value (p:t) (thi:int) (x:Label.t) : t list = begin
  (* ret := x.data *)
    let ix = index p thi x in
    check_dereferencing p thi ix (sprintf "ret := %s" (Label.string_of x));
    let color =
      try
	for ic = p.gvar to p.gvar + p.colors - 1 do
	  match p.heap.(ix).(ic) with | Equal -> raise (Found ic) (* assuming precision *) | _ -> ()
	done;
	Data.neutral (* I didn't find anything equal... must be white *)
      with Found i -> (*just for data type*) Data.reconstruct (i - p.gvar, p.translation.(i))
    in
    p.threads.(thi).return <- color;
    [p]
  end
(* No need to clone *)
  let reset_return_value (p:t) (thi:int) : t list = begin
  (* ret := star  *)
    p.threads.(thi).return <- Data.top;
    [p]
  end


(* No need to clone *)
  let data_assign_var (p:t) (thi:int) (x:Label.t) (y:Label.t) : t list = begin
    failwith("Don't use it")
(*   (\* x.data := y *\) *)
(*   check_dereferencing p thi x; *)

(*   (\* CHEAT and MAKE IT STAR *\) *)
(*   [] *)
  end

(* No need to clone *)
  let assign (p:t) (thi:int) (x:Label.t) (y:Label.t) : t list = begin
  (* x := y *)
    let ix, iy = index p thi x, index p thi y in
    _assign p ix iy;
    [p]
  end

(* No need to clone *)
  let assign_dot_next (p:t) (thi:int) (x:Label.t) (y:Label.t) : t list = begin
  (* x := y.next *)

  (* Fetching the immediate successor *)
    let iy = index p thi y in
    check_dereferencing p thi iy (sprintf "%s := %s.next" (Label.string_of x) (Label.string_of y));
    let succs = _succs p iy in
    let ix = index p thi x in

    match succs with
    | [] -> failwith("can't be")
    | [isucc] when ix = isucc -> 
	(* Reset the edge to be a one-step edge! *)
	_remove_edge p iy ix;
	_add_edge p iy ix OneStep;
	[p]
    | isucc'::tail -> begin
	
	let isucc = if ix = isucc' then List.hd tail else isucc' in

	match p.heap.(iy).(isucc) with
	| OneStep -> (* It is one step-away *)
            (* Placing x as isucc, the immediate successor of y *)
	    if not(List.mem ix succs) then _assign p ix isucc;
	    [p]
	| Reach -> (* The successors are many steps away *)

	    let p' = clone p in

            (* Placing x as isucc, the immediate successor of y *)
	    if not(List.mem ix succs) then _assign p' ix isucc;
	    (* But I should reset to a one-step successor *)
	    (* We know that doesn't change the join information, but the pc might change *)
	    _remove_edge p' iy ix;
	    _add_edge p' iy ix OneStep;
	    
            (* Placing x in between y and isucc *)
	    _remove_edge p iy isucc;
	    _remove_label p ix;
	    _add_edge p ix isucc Reach;
	    _add_edge p iy ix OneStep;
	    p.freecells.(ix) <- false; (* I make x (alone) not deallocated anyway *)
	
	    [p;p']
	| _ -> failwith("Que? Should be a successor...")
    end
  end

(* No need to clone *)
  let dot_next_assign (p:t) (thi:int) (x:Label.t) (y:Label.t) : t list = begin
  (* x.next := y *)

    let ix,iy = index p thi x, index p thi y in
    check_dereferencing p thi ix (sprintf "%s.next := %s" (Label.string_of x) (Label.string_of y));
    assert( ix <> iy );

    let succs = _succs p ix in
(*     if not(List.mem iy succs) then begin *)
      _remove_edge p ix (List.hd succs);
      _add_edge p ix iy OneStep;
(*     end; *)
    [p]
    (* Nothing to do for the allocations *)
  end

(* No need to clone *)
  let make_new_cell (p:t) (thi:int) (x:Label.t) : t list = begin
    assert( Label.is_local x );
    assert( is_sane p );

    let ix = index p thi x in

    let res = ref [] in
  (* I inspect all free cells, I allocate them, and assign x to each *)
    for i=0 to p.bound do
      if p.freecells.(i) then begin
	let p' = clone p in
	for j=0 to p.bound do match p.heap.(i).(j) with | Equal -> p'.freecells.(j) <- false; | _ -> () done;
	_assign p' ix i;
	res := p' :: !res; (* it might create many same copies, but I don't care *)
      end;
    done;

    (* Last one: I add a new cell *)
    _remove_label p ix; (* p.freecells.(ix) <- false; *)
    (* Make it reach anything that iBottom is equal to *)
    (* No need to call _add_edge *)
    let iBottom = index p thi Label.bottom in
    for j=0 to p.bound do
      match p.heap.(iBottom).(j) with
      | Equal -> (* Anything that is equal to iBottom *)
	  p.heap.(ix).(j) <- OneStep;
      | _ -> ()
    done;

    p :: !res
  end

(* No need to clone *)
  let free_cell (p:t) (thi:int) (x:Label.t) : t list = begin

    let ix = index p thi x in
    check_dereferencing p thi ix (sprintf "free(%s)" (Label.string_of x));

    let iBottom = index p thi Label.bottom in
    let succs = _succs p ix in
(*     if not(List.mem iBottom succs) then begin *)
      _remove_edge p ix (List.hd succs);
      _add_edge p ix iBottom OneStep;
(*     end; *)

    (* Make the ones equal to ix free cells *)
    for i=0 to p.bound do match p.heap.(ix).(i) with | Equal -> p.freecells.(i) <- true; | _ -> () done;

    [p]
  end

(* No need to clone *)
  let init_thread p thi vars : t list = begin
    assert( p.threads.(thi).var = 0 );

    assert( try for i=0 to Array.length p.threads.(thi).bits - 1 do if p.threads.(thi).bits.(i) then raise Stop; done; true with Stop -> to_dot p "tmp/ouch"; false ); 

    let count = Array.length vars in
    let newBound = p.bound+count in
    let cut = begin
      let shift = ref 0 in
      for i=0 to p.nth - 1 do if i<thi then shift := p.threads.(i).var + !shift; done;
      p.gvar + p.colors + !shift
    end in
    
    let h = Array.make_matrix (newBound+1) (newBound+1) NoInfo in
    
    for i=0 to cut - 1 do
      for j=0 to cut - 1 do (* Copy the colors and globals *) h.(i).(j) <- p.heap.(i).(j); done;
      for j=cut to p.bound do (* Taking care of the threads *) h.(i).(j+count) <- p.heap.(i).(j); done;
    done;

    for i=cut to p.bound do
      for j=0 to cut - 1 do h.(i+count).(j) <- p.heap.(i).(j); done;
      for j=cut to p.bound do h.(i+count).(j+count) <- p.heap.(i).(j); done;
    done;

  (* assign them to bottom *)
    let iBottom = index p thi Label.bottom in
    for i=cut to cut + count - 1 do h.(iBottom).(i) <- Equal; done;
    for i=cut to cut + count - 1 do for j=0 to newBound do h.(i).(j) <- h.(iBottom).(j); done; done;
    for i=cut to cut + count - 1 do h.(i).(iBottom) <- Equal; done;
    for i=cut to cut + count - 1 do for j=0 to newBound do h.(j).(i) <- h.(j).(iBottom); done; done;

    let freecells = Array.make (newBound+1) false in
    for i=0 to cut - 1 do freecells.(i) <- p.freecells.(i); done;
    for i=cut to p.bound do freecells.(i+count) <- p.freecells.(i); done;
  (* between cut and cut+count-1, it's already false *)

    let trans = Array.make (newBound+1) "" in
    for i=0 to cut - 1 do trans.(i) <- p.translation.(i); done;
    for i=cut to p.bound do trans.(i+count) <- p.translation.(i); done;
    for i=0 to count - 1 do assert( i = Label.unpack vars.(i) ); trans.(cut+i) <- Label.string_of vars.(i); done;

    p.translation <- trans;
    p.bound <- newBound;
    p.heap <- h;
    p.freecells <- freecells;
    p.threads.(thi).var <- count;

    [p]
  end

(* No need to clone *)
  let kill_thread (p:t) (thi:int) : t list = begin

    let th = p.threads.(thi) in

    let newBound = p.bound - th.var in

    let h = Array.make_matrix (newBound+1) (newBound+1) NoInfo in

    let cut = begin
      let shift = ref 0 in
      for i=0 to p.nth - 1 do if i<thi then shift := p.threads.(i).var + !shift; done;
      p.gvar + p.colors + !shift
    end in

  (* Removing the thread labels, but also clean its vertices if necessary *)
    for i=cut to cut + th.var-1 do _remove_label p i; done;

  (* Copying to the new heap. AFTER the label removing!! *)
    for i=0 to cut - 1 do
      for j=0 to cut - 1 do h.(i).(j) <- p.heap.(i).(j); done;
      for j=cut to newBound do h.(i).(j) <- p.heap.(i).(j+th.var); done;
    done;
    for i=cut to newBound do
      for j=0 to cut - 1 do h.(i).(j) <- p.heap.(i+th.var).(j); done;
      for j=cut to newBound do h.(i).(j) <- p.heap.(i+th.var).(j+th.var); done;
    done;
    
  (* Work on freecells and colors *)
    let freecells = Array.make (newBound+1) false in
    for i=0 to cut - 1 do freecells.(i) <- p.freecells.(i); done;
    for i=cut to newBound do freecells.(i) <- p.freecells.(i+th.var); done;

    let trans = Array.make (newBound+1) "" in
    for i=0 to cut - 1 do trans.(i) <- p.translation.(i); done;
    for i=cut to newBound do trans.(i) <- p.translation.(i+th.var); done;

    p.bound <- newBound;
    p.heap <- h;
    p.translation <- trans;
    p.freecells <- freecells;
    _reset_thread p.threads.(thi);

    [p]
  end

  let concretize_data p thi v data = begin
    if Data.is_interesting data then begin
      let iv = index p thi v in
      let iData = p.gvar + Data.unpack data in
    (* assigning the color to iv *)
      for i=0 to p.bound do
	p.heap.(iData).(i) <- p.heap.(iv).(i); (* Erase line, replace with iy *)
	p.heap.(i).(iData) <- p.heap.(i).(iv); (* Same with column *)
      done;
      p.heap.(iData).(iData) <- Equal;
      p.heap.(iData).(iv) <- Equal; (* Note: should not be needed here *)
      p.heap.(iv).(iData) <- Equal;
      p.freecells.(iData) <- p.freecells.(iv); (* allocation *)
    end;
  end

(* Must clone when needed *)
  let validate_insert (porg:t) (thi:int) (var:Label.t) (all: (Observer.data * Observer.state) list ) : t list  = begin
    List.fold_left (fun acc (data_,s) -> match data_ with
    | Observer.NoData | Observer.State _ ->  failwith("that's a weird observer transition")
    | Observer.ObsData data -> begin
	match promise porg thi with
	| Promise.Insert dlist ->
	    List.fold_left (fun acc' d -> if Data.equal data d then begin
	      let p = clone porg in
	      set_observer p s;
	      concretize_data p thi var d;
	      reset_promise p thi;
	      p::acc
	    end else acc') acc dlist
	| _ -> acc (* wrong promise *)
    end) [] all
  end

(* Must clone when needed *)
  let validate_delete (porg:t) (thi:int) (all: (Observer.data * Observer.state) list ) : t list  = begin
    List.fold_left (fun acc (data,s) -> match data with
    | Observer.NoData | Observer.State _ ->  failwith("that's a weird observer transition")
    | Observer.ObsData d -> begin
	if Data.compatible porg.threads.(thi).return d then begin
	  let p = clone porg in
	(* p.threads.(thi).return <- d; *)
	  set_observer p s;
	  reset_promise p thi;
	  p::acc
	end else acc (* wrong promise *)
    end) [] all
  end

(* Must clone when needed *)
  let validate_empty (porg:t) (thi:int) (all: (Observer.data * Observer.state) list ) : t list  = begin
    List.fold_left (fun acc (data,s) -> match data with
    | Observer.ObsData _ | Observer.NoData ->  failwith("that's a weird observer transition")
    | Observer.State s' -> begin
	match promise porg thi with
	| Promise.ReturnEmpty obs when Observer.same_state obs s' ->
	    let p = clone porg in
	    set_observer p s;
	    reset_promise p thi;
	    p::acc
	| _ -> acc (* not the right promise: DIE !!! *)
    end) [] all
  end

(* Must clone when needed *)
  let main_lock porg thi lock = begin
    (* assert( not(porg.lockstates.(lock).(thi)) ); (\* we don't want to lock again *\) *)
    let locked = ref false in
    for t=0 to porg.nth - 1 do if porg.lockstates.(lock).(t) then locked := true; done;
    if !locked then [] else begin
      let p = clone porg in
      p.lockstates.(lock).(thi) <- true;
      [p]
    end
  end

  let main_unlock porg thi lock = begin
    assert( porg.lockstates.(lock).(thi) ); (* we don't want to unlock a free lock *)
    let p = clone porg in
    p.lockstates.(lock).(thi) <- false;
    [p]
  end

(* =================================================================================== *)

  let create_queue nth (head:Label.t) (tail:Label.t) colors bits locks = begin

    assert( 2 = Label.unpack head && 3 = Label.unpack tail );
    let c = create nth [|head;tail|] colors bits locks in

    let iNull = index c (-1) Label.nil in
    let iHead = index c (-1) head in
    let iTail = index c (-1) tail in
    
    c.heap.(iHead).(iNull) <- OneStep;
    c.heap.(iTail).(iNull) <- OneStep;

    c.heap.(iHead).(iHead) <- Equal;
    c.heap.(iTail).(iTail) <- Equal;

    c.heap.(iHead).(iTail) <- Equal;
    c.heap.(iTail).(iHead) <- Equal;

    sanitize c;
    [c]

(*     let c' = create nth [|head;tail|] colors bits in *)

(*     let iNull' = index c' (-1) Label.nil in *)
(*     let iHead' = index c' (-1) head in *)
(*     let iTail' = index c' (-1) tail in *)
    
(*     c'.heap.(iHead').(iTail') <- Reach; *)
(*     c'.heap.(iTail').(iNull') <- OneStep; *)

(*     c'.heap.(iHead').(iHead') <- Equal; *)
(*     c'.heap.(iTail').(iTail') <- Equal; *)

(*     sanitize c'; *)

(*     [c;c'] *)
  end

  let create_stack nth (top:Label.t) colors bits locks = begin

    assert( 2 = Label.unpack top );
    let c = create nth [|top|] colors bits locks in

    let iNull = index c (-1) Label.nil in
    let iTop = index c (-1) top in
    
    c.heap.(iTop).(iNull) <- Equal;
    c.heap.(iNull).(iTop) <- Equal;
    c.heap.(iTop).(iTop) <- Equal;

    sanitize c;
    [c]
  end

(* let create_empty_buckets _ _ = [] *)

  let fake _ = begin
    let head = Label.global (2,"H") in
    let tail = Label.global (3,"T") in
    let h0 = Label.local (0,"h") in
    let t0 = Label.local (1,"t") in
    let next0 = Label.local (2,"next") in
    
    let h = Array.make_matrix 8 8 NoInfo in
    let freecells = Array.make 8 false in
    let c = {
      nth = 2;
      threads = Array.init 2 (fun _ -> thread_create 0);
      heap = h;
      freecells=freecells;
      gvar = 4;
      colors = 1;
      bound = 7;
      lockstates = (Array.make_matrix 0 2 false);
      locks=(-1);

      encoding=""; (* to be sanitized *)
      
      translation = [|Label.string_of Label.nil;Label.string_of Label.bottom;"H";"T";"R";"h";"t";"next";|];

      id = 0;
      messages = [];
      alive = true;
      observer = Observer.init;
      parent = None;
    } in

    let iNull = index c 0 Label.nil in
    let iHead = index c 0 head in
    let iTail = index c 0 tail in
    let ih0 = index c 0 h0 in
    let it0 = index c 0 t0 in
    let inext0 = index c 0 next0 in

    c.threads.(0).var <- 3;
    c.threads.(0).pc <- 110;
    c.threads.(0).return <- Data.neutral;
    
    h.(iHead).(iTail) <- OneStep;
    h.(iHead).(it0) <- OneStep;
    h.(iHead).(inext0) <- OneStep;
    
    for i=0 to 7 do h.(i).(i) <- Equal; done;

    h.(iHead).(ih0) <- Equal;
    h.(ih0).(iHead) <- Equal;

    h.(ih0).(iTail) <- OneStep;
    h.(ih0).(it0) <- OneStep;
    h.(ih0).(inext0) <- OneStep;

    h.(iHead).(iTail) <- OneStep;
    h.(iHead).(it0) <- OneStep;
    h.(iHead).(inext0) <- OneStep;
    
    h.(iTail).(it0) <- Equal;
    h.(iTail).(inext0) <- Equal;
    h.(it0).(iTail) <- Equal;
    h.(it0).(inext0) <- Equal;
    h.(inext0).(iTail) <- Equal;
    h.(inext0).(it0) <- Equal;

    h.(iTail).(iNull) <- OneStep;
    h.(it0).(iNull) <- OneStep;
    h.(inext0).(iNull) <- OneStep;

    sanitize c;
    c
  end

let view _ _ = failwith("not implemented")
let build_key _ = failwith("not implemented")
let extend _ _ _ = failwith("not implemented")
let trim _ = failwith("not implemented")
let is_more_general _ _ = failwith("not implemented")

end (* !module Matrix - with one step *)


module Joined : Constraint.C = struct

  let name = "Matrix - with one step successor - and joined information"

  exception Found of int
  exception Stop (* to break foldings and iterations *)
      
(* Global counter, for identification *)  
  let maxID = ref (-1)

(* ========================================================================== *)
  type thread = {
      mutable var:int;
      mutable pc: int;
      mutable promise: Promise.t;
      mutable return: Data.t;
    (* mutable stack: Stack.t; *)
      mutable bits: bool array;
    }

  let thread_create b = begin
    {pc=0;var=0;promise=Promise.NoPromise;return=Data.top;bits=(Array.make b false);(* stack=Stack.create 1; *) (* One argument in the stack *)}; 
  end
      
  let thread_to_dot th =
    sprintf "PC: %d     Promise: %s   Return: %s   Bits:[|%s]"
      th.pc (Promise.string_of th.promise) (Data.string_of th.return) (Array.fold_left (sprintf "%s%B|") "" th.bits)

  let encode_thread th =
    sprintf "%d-%s-%s-%s"
      th.pc (Promise.string_of th.promise) (Data.string_of th.return) (Array.fold_left (sprintf "%s%B|") "Bits=|" th.bits)


(* ========================================================================== *)
  type t = {

      mutable nth:int;
      mutable threads: thread array;
      mutable heap: Info.t array array;
      mutable freecells: bool array;
      mutable bound: int;
      gvar: int;
      colors:int;
      mutable lockstates: bool array array;
      locks: int;

      mutable translation: string array;

      mutable observer: Observer.state;      (** The state of the observer *)

      mutable encoding: string;

      id:int;
      mutable messages:string list;
      mutable alive: bool;
      mutable in_queue: bool;
      mutable parent: t option;
    } 
	
  let create nth gvars gcolors b locks = incr maxID;
    let gvar = 2 + Array.length gvars in
    let colors = Array.length gcolors in
    let bound = gvar + colors in
    let zero = Info.create [] in
    let h = Array.make_matrix bound bound zero in
    for i=0 to bound - 1 do for j=0 to bound - 1 do h.(i).(j) <- Info.clone h.(i).(j); done; done;
    for i=0 to bound - 1 do for j=0 to bound - 1 do  Info.set h.(i).(j) (if i=j then Info.Equal else Info.Unrelated); done; done;
    let freecells = Array.make bound false in
    {
    nth = nth;
    threads = Array.init nth (fun _ -> thread_create b);
    heap = h;
    freecells=freecells;
    gvar = gvar;
    colors = colors;
    bound = gvar + colors - 1;
    lockstates = (Array.make_matrix locks nth false);
    locks = locks - 1;

    encoding=""; (* to be sanitized *)

    translation = Array.append
      (Array.map Label.string_of (Array.append [|Label.nil;Label.bottom|] gvars))
      (Array.map Data.string_of gcolors);

    id = (!maxID);
    messages = [];
    alive = true;
    in_queue=false;
    observer = Observer.init;
    parent = None;
  }

(*   let start_globals p = 0 *)
(*   let end_globals p = p.gvar - 1 *)
(*   let start_colors p = p.gvar *)
(*   let end_colors p = p.gvar + p.colors - 1 *)

  let clone t = assert( t.alive ); incr maxID;
    { t with id=(!maxID);
      threads = Array.map (fun th -> {th with bits=Array.copy th.bits;}) t.threads;
      heap = Array.map (Array.map Info.clone) t.heap;
      freecells = Array.copy t.freecells;
      lockstates = Array.map Array.copy t.lockstates;
      translation = Array.copy t.translation;
      (* will copy the rest *) 
    }

  let string_of_locks p = begin
    let str = ref "" in
    for lock=0 to p.locks do
      for t=p.nth-1 downto 0 do
	str := sprintf "%s%s|" !str (if p.lockstates.(lock).(t) then "L" else "_");
      done;
      str := !str ^ "#";
    done;
    !str
  end

  let string_of t =
    sprintf "%s[Observer=%s,%s]" (if t.alive then "" else "(deleted)")
      (Observer.string_of_state t.observer)
      (Array.fold_left (fun acc th -> sprintf "%s%s|" acc (encode_thread th)) "" t.threads)

(* ========================================================================================================= *)
(* =====================                        Printing                            ======================== *)
(* ========================================================================================================= *)

  let __t p i = begin
    let shift = ref (p.gvar + p.colors) in
    if i < !shift then p.translation.(i) else begin
      try for t=0 to p.nth - 1 do if i < !shift + p.threads.(t).var then raise (Found t) else shift := p.threads.(t).var + !shift; done; "unknown"
      with Found thi -> sprintf "%s.%d" p.translation.(i) thi
    end
  end

  let to_dot (p:t) (where:string) = begin
    
    let info = 
      sprintf "%s<p>ID: %d</p><p>Parent: %s</p><p>Encoding: %s</p><ol reversed>%s</ol>"
	(if p.alive then "" else "<p>Deleted</p>")
	p.id
	(match p.parent with None -> "orphelin" | Some papa -> string_of_int papa.id)
	p.encoding
	(List.fold_right (sprintf "<li>%s</li>%s") p.messages "")
    in

    let threads = ref "<div id=\"threads\">" in
    Array.iteri (fun thi th -> threads := sprintf "%s<p>Th %d: %s</p>" !threads thi (thread_to_dot th);) p.threads;
    threads := !threads ^ "</div>";

    let gbound = p.gvar + p.colors - 1 in

    let heap = ref "<table><thead><tr><th></th>" in
    for i=0 to gbound do
      heap := sprintf "%s<th>%s</th>" !heap p.translation.(i);
    done;
    let shift = ref (gbound + 1) in
    for t=0 to p.nth - 1 do
      for i = !shift to !shift + p.threads.(t).var - 1 do
	heap := sprintf "%s<th>%s<sub>%d</sub></th>" !heap p.translation.(i) t;
      done;
      shift := !shift + p.threads.(t).var;
    done;
    heap := !heap ^ "</tr></thead><tbody>";

    for i=0 to gbound do
      heap := sprintf "%s<tr><td class=\"name\">%s</td>" !heap p.translation.(i);
      for j=0 to p.bound do
	if j=i
	then heap := sprintf "%s<td></td>" !heap
	else heap := sprintf "%s<td style=\"background-color:%s;\">%s</td>" !heap (if j>i then "#A4D7EB" else "#FFCB40") (Info.to_dot p.heap.(i).(j));
      done;
      heap := !heap ^ "</tr>";
    done;
    shift := gbound + 1;
    for t=0 to p.nth - 1 do
      for i = !shift to !shift + p.threads.(t).var - 1 do
	heap := sprintf "%s<tr><td class=\"name\">%s<sub>%d</sub></td>" !heap p.translation.(i) t;
	for j=0 to p.bound do
	  if j=i
	  then heap := sprintf "%s<td></td>" !heap
	  else heap := sprintf "%s<td style=\"background-color:%s;\">%s</td>" !heap (if j>i then "#A4D7EB" else "#FFCB40") (Info.to_dot p.heap.(i).(j));
	done;
	heap := !heap ^ "</tr>";
      done;
      shift := !shift + p.threads.(t).var;
    done;
    heap := !heap ^ "</tbody></table>";
    
    let freecells = ref "<table><thead><tr>" in
    for i=0 to gbound do
      freecells := sprintf "%s<th>%s</th>" !freecells p.translation.(i);
    done;
    shift := gbound + 1;
    for t=0 to p.nth - 1 do
      for i = !shift to !shift + p.threads.(t).var - 1 do
	freecells := sprintf "%s<th>%s<sub>%d</sub></th>" !freecells p.translation.(i) t;
      done;
      shift := !shift + p.threads.(t).var;
    done;
    freecells := !freecells ^ "</tr></thead><tbody><tr>";
    for i=0 to p.bound do
      freecells := sprintf "%s<td>%s</td>" !freecells (if p.freecells.(i) then "x" else "");
    done;
    freecells := !freecells ^ "</tr></tbody></table>";

    let locks = ref "<table><thead><tr><th></th>" in
    for t=0 to p.nth - 1 do
      locks := sprintf "%s<th>Th<sub>%d</sub></th>" !locks t;
    done;
    locks := !locks ^ "</tr></thead><tbody>";
    for i=0 to p.locks do
      locks := sprintf "%s<tr><td>Lock<sub>%d</sub></td>" !locks i;
      for t=0 to p.nth - 1 do
	locks := sprintf "%s<td>%s</td>" !locks (if p.lockstates.(i).(t) then "o" else "");
      done;
      locks := sprintf "%s</tr>" !locks;
    done;
    locks := !locks ^ "</tbody></table>";

    let css = "table{ border-collapse:collapse; margin:0 auto; } td { border: 1px solid black; padding:10px; text-align:center; min-width:30px; } th,table td.name {background:black; color:white; border: 1px solid white; padding:10px; text-align:center; min-width:30px; }" in

    let res = sprintf "<html><head><meta charset=\"utf-8\"/><style>%s</style></head><body>%s<p>Observer: %s</p><hr/>%s<hr/>%s<hr/>%s<hr/>%s</body></html>"
	css !threads (Observer.string_of_state p.observer) !heap !freecells !locks info
    in
    let oc = open_out (where ^ ".html") in Printf.fprintf oc "%s" res; close_out oc;

  end


(* ========================================================================================================= *)
(* =====================                        Utilities                           ======================== *)
(* ========================================================================================================= *)
      
  let id t = t.id
  let observer t = t.observer
  let set_observer t obs = t.observer <- obs
      
  let log t message = t.messages <- message::t.messages
(*   let log t message = t.messages <- [message] *)

  let nthreads p = p.nth

  let is_alive t = t.alive
  let delete t = t.alive <- false

  let set_in_queue t v = t.in_queue <- v
  let in_queue t = t.in_queue
  let set_in_slice _ _ = failwith("not implemented")
  let in_slice _ = failwith("not implemented")

  let set_parent p p' = p.parent <- Some p'
  let parent p = match p.parent with None -> failwith("no parent") | Some papa -> papa

  let pc p thi = p.threads.(thi).pc
  let set_pc p thi pc = p.threads.(thi).pc <- pc  

  let promise p thi = p.threads.(thi).promise
  let set_promise p thi prom = p.threads.(thi).promise <- prom
  let reset_promise p thi = set_promise p thi Promise.NoPromise

  let _reset_thread th = begin
    th.var     <- 0;
    th.pc      <- 0;
    th.promise <- Promise.NoPromise;
    th.return  <- Data.top;
    for i=0 to Array.length th.bits - 1 do th.bits.(i) <- false done;
  end

  let rec iter_trace p f = begin
    f p;
    match p.parent with
    | Some papa when papa != p (*physically*) -> iter_trace papa f
    | _ -> ()
  end

  let print_trace p where = iter_trace p (fun p' -> to_dot p' (sprintf "%s-%d" where (id p')))

(* ========================================================================================================= *)
(* =====================                       Entailement                          ======================== *)
(* ========================================================================================================= *)

  let hash p = Hashtbl.hash p.encoding
  let equal p1 p2 = p1.encoding = p2.encoding

(* =================================================================================== *)
  let index p thi v = begin
    if Label.is_global v then Label.unpack v else begin
      let shift = ref 0 in
      for i = 0 to thi - 1 do shift := !shift + p.threads.(i).var done; (*shouldn't count when thi=0 *)
      p.gvar + p.colors + !shift + (Label.unpack v)
    end
  end

(* =================================================================================== *)

  exception NullPointerDereferencing of t * string
  exception DoubleFree of t * string
  exception Dangling of t * string
  exception ClashWithInit of t

  let check_dereferencing p thi i str = begin
    if Info.is p.heap.(i).(index p thi Label.nil) Info.Equal then raise (NullPointerDereferencing (p,str));
    if Info.is p.heap.(i).(index p thi Label.bottom) Info.Equal then raise (Dangling (p,str));
  end

(* ========================================================================================================= *)
(* =====================                        Sanity check                        ======================== *)
(* ========================================================================================================= *)

  exception Insane of t * string

  let _check_sanity p = begin
    for i=0 to p.bound do
      for j=0 to p.bound do
	if Info.is_empty p.heap.(i).(j) then raise (Insane (p,sprintf "Empty? %s,%s" (__t p i) (__t p j)));
(* 	if p.freecells.(i) <> p.freecells.(j) && Info.is p.heap.(i).(j) Info.Equal then raise (Insane (p,sprintf "Allocation %s,%s" (__t p i) (__t p j))); *)

	if i <> j && p.freecells.(i) && p.freecells.(j) && Info.is p.heap.(i).(j) Info.Equal then raise (Insane (p,sprintf "Allocation %s,%s" (__t p i) (__t p j)));


(* 	if Info.is p.heap.(i).(j) Info.Equal then begin *)
(* 	  for k=0 to p.bound do *)
(* 	    if Info.is p.heap.(i).(k) Info.Equal && not(Info.is p.heap.(k).(j) Info.Equal) *)
(* 	    then raise (Insane (p,sprintf "Equal: %s,%s,%s" (__t p i) (__t p j) (__t p k))); (\* Equality *\) *)
(* 	  done; *)
(* 	end; *)

(* 	if Info.is p.heap.(i).(j) Info.Reaches then begin *)
(* 	  for k=0 to p.bound do *)
(* 	    if Info.is p.heap.(j).(k) Info.Equal && not(Info.is p.heap.(i).(k) Info.Reaches) *)
(* 	    then raise (Insane (p,sprintf "Equal+Reach %s,%s,%s" (__t p i) (__t p j) (__t p k))); (\* Equality + Reach *\) *)

(* 	    if Info.is p.heap.(i).(k) Info.Equal && not(Info.is p.heap.(k).(j) Info.Reaches) *)
(* 	    then raise (Insane (p,sprintf "Equal+Reach %s,%s,%s" (__t p i) (__t p j) (__t p k))); (\* Equality + Reach *\) *)

(* 	    if Info.is p.heap.(i).(k) Info.Reaches && not(Info.is p.heap.(j).(k) Info.Equal) *)
(* 	    then raise (Insane (p,sprintf "Equal+Reach %s,%s,%s" (__t p i) (__t p j) (__t p k))); (\* Equality + Reach *\) *)
(* 	  done; *)
(* 	end; *)

(* 	if (\* i =/= j *\) *)
(* 	  Info.is p.heap.(i).(j) Info.Unrelated || *)
(* 	  Info.is p.heap.(i).(j) Info.Reaches || *)
(* 	  Info.is p.heap.(i).(j) Info.ReachesMore || *)
(* 	  Info.is p.heap.(i).(j) Info.IsReached || *)
(* 	  Info.is p.heap.(i).(j) Info.IsReachedMore *)
(* 	then  *)
(* 	  for k=0 to p.bound do *)
(* 	    if Info.is p.heap.(i).(k) Info.Equal && Info.is p.heap.(k).(j) Info.Equal *)
(* 	    then raise (Insane (p,sprintf "Equal: %s,%s,%s" (__t p i) (__t p j) (__t p k))); (\* Equality *\) *)
(* 	  done; *)

      done;
    done;
  end

(*   let _in_global_world p iv = begin (\* Color or Label *\) *)
(*     let rec fetch i = begin *)
(*       if i < p.gvar then raise Stop; *)
(*       let preds = _preds p i in *)
(*       List.iter fetch preds; *)
(*     end in try fetch iv; false with Stop -> true *)
(*   end *)

  let _check_colors p = begin
    for c1 = p.gvar to p.gvar + p.colors - 1 do
      for c2 = p.gvar to p.gvar + p.colors - 1 do
	if c1 <> c2 && Info.is p.heap.(c1).(c2) Info.Equal then raise (Insane (p,sprintf "Colors %s and %s can be equal?" (__t p c1) (__t p c2)));
      done;
    done;
  end
	
  let _check_diagonal p = begin
    for i=0 to p.bound do if not(Info.is_only p.heap.(i).(i) Info.Equal) then raise (Insane (p,sprintf "Wrong diagonal: %s [%s]" (__t p i) (Info.string_of p.heap.(i).(i)))); done;
  end

  let _check_symmetry p = begin
    for i=0 to p.bound do for j=0 to p.bound do
      if not(Info.is_symmetric p.heap.(i).(j) p.heap.(j).(i)) then raise (Insane (p,sprintf "Symmetry: %s <> %s" (__t p i) (__t p j)));
    done; done;
  end

  let _check_succ_of_nil_and_bottom p = begin
    let iBottom = index p (-1) Label.bottom in
    let iNull = index p (-1) Label.nil in
    for i = 0 to p.bound do
      if 
	Info.is p.heap.(iBottom).(i) Info.Reaches || Info.is p.heap.(iNull).(i) Info.Reaches ||
	Info.is p.heap.(iBottom).(i) Info.ReachesMore || Info.is p.heap.(iNull).(i) Info.ReachesMore
      then raise (Insane (p,"Outgoing null or bottom??"));
    done;
  end

  exception Inconsistent
  let rec strengthen p x y phi : unit = begin
(*     if debug then Debug.print "strengthening (%s,%s) %s with %s\n" (__t p x) (__t p y) (Info.string_of p.heap.(x).(y)) (Info.string_of phi); *)
    assert( x <> y );
    
    let str = Info.string_of p.heap.(x).(y) in
    if Info.strengthen p.heap.(x).(y) phi then begin
      Info.update_diagonal p.heap.(y).(x) p.heap.(x).(y);
      if debug then Debug.print "strengthening (%s,%s) %s with %s becomes %s\n" (__t p x) (__t p y) str (Info.string_of phi) (Info.string_of p.heap.(x).(y));

      if Info.is_empty p.heap.(x).(y) then begin
	if debug then begin
	  Debug.print "(%s,%s)[%s] is empty (from %s, strengthened with %s)\n" (__t p x) (__t p y) (Info.string_of p.heap.(x).(y)) str (Info.string_of phi);
	  Debug.print "%s Ouch, %d is inconsistent %s\n" Debug.red p.id Debug.noColor;
	end;
	raise Inconsistent;
      end;

      (* Propagation *)
      for z=0 to p.bound do if z <> x && z <> y then begin
	if debug then Debug.print "propagation x:%s   y:%s   z:%s\n" (__t p x) (__t p y) (__t p z);
	strengthen p x z (Info.merge p.heap.(x).(y) p.heap.(y).(z));
	strengthen p z y (Info.merge p.heap.(z).(x) p.heap.(x).(y));
      end; done;
    end else if debug then Debug.print "(%s,%s) %s has not changed with %s\n" (__t p x) (__t p y) str (Info.string_of phi); (* it has not changed *)
  end

(*   let rec strengthen p x y phi : unit = begin *)
(* (\*     if debug then Debug.print "strengthening (%s,%s) %s with %s\n" (__t p x) (__t p y) (Info.string_of p.heap.(x).(y)) (Info.string_of phi); *\) *)
(*     assert( x <> y ); *)
    
(*     let str = Info.string_of p.heap.(x).(y) in *)
(*     if Info.strengthen p.heap.(x).(y) phi then begin *)
(*       Info.update_diagonal p.heap.(y).(x) p.heap.(x).(y); *)
(*       if debug then Debug.print "strengthening (%s,%s) %s with %s becomes %s\n" (__t p x) (__t p y) str (Info.string_of phi) (Info.string_of p.heap.(x).(y)); *)

(*       if Info.is_empty p.heap.(x).(y) then begin *)
(* 	Debug.print "(%s,%s)[%s] is empty (from %s, strengthened with %s)\n" (__t p x) (__t p y) (Info.string_of p.heap.(x).(y)) str (Info.string_of phi); *)
(* 	Debug.print "%s Ouch, %d is inconsistent %s\n" Debug.red p.id Debug.noColor; *)
(* 	raise Inconsistent; *)
(*       end; *)

(*       (\* Propagation *\) *)
(*       for z=0 to p.bound do if z <> x && z <> y then begin *)
(* 	if debug then Debug.print "propagation x:%s   y:%s   z:%s\n" (__t p x) (__t p y) (__t p z); *)
(* 	propagate p x y z; *)
(* 	propagate p z x y; *)
(*       end; done; *)
(*     end else if debug then Debug.print "(%s,%s) %s has not changed with %s\n" (__t p x) (__t p y) str (Info.string_of phi); (\* it has not changed *\) *)
(*   end *)
(*   and propagate p a b c = begin *)
(*     assert( a <> c ); *)
(*     let phi_ab = p.heap.(a).(b) in *)
(*     let phi_bc = p.heap.(b).(c) in *)
(*     let phi_ac = Info.merge phi_ab phi_bc in *)
(*     if debug then Debug.level (1); *)
(*     strengthen p a c phi_ac; *)
(*     if debug then Debug.level (-1); *)
(*   end *)

  let rec _check_consistency (i,j) p = begin

    if Info.is_empty p.heap.(i).(j) then raise (Insane (p,"Inconsistent"));

    let all =
      if i=j 
      then [p] 
      else begin
	match Info.split p.heap.(i).(j) with
	| [] -> failwith("impossible")
	| [info] -> [p]
	| all_possibilities -> 
	    List.fold_left (fun acc info -> begin
		let p' = clone p in
		log p' (sprintf "Checking consistency by strengthening (%s , %s) with %s" (__t p' i) (__t p' j) (Info.string_of info));
		if debug then Debug.print "%s Checking consistency on %d (clone from %d) by strengthening (%s , %s) with %s %s\n"
		    Debug.yellow (id p') (id p) (__t p' i) (__t p' j) (Info.string_of info) Debug.noColor;
		set_parent p' p;
		try
		  Debug.level (1);
		  strengthen p' i j info;
		  Debug.level (-1);
		  p'::acc
		with Inconsistent -> Debug.level (-1); acc
	    end) [] all_possibilities
      end
    in

    if List.length all = 0 then raise (Insane (p,"Inconsistent"));

    match i<p.bound, j<p.bound with
    | true, true -> List.iter (_check_consistency (i,j+1)) all 
    | true, false -> List.iter (_check_consistency (i+1,0)) all 
    | false, _ -> ()
  end

  let is_sane (p:t) : bool = begin
  (* TO BE COMPLETED *)
    try
      _check_diagonal p;
(*       _check_succ_of_nil_and_bottom p; *)

(*       _check_consistency (0,1) p; *)

      _check_sanity p;
      _check_symmetry p;
      _check_colors p;
      true
    with Insane (c,str) -> Debug.print "%s %d is INSANE %s %s\n" Debug.red c.id Debug.noColor str; print_trace c "tmp/insane"; false
  end

(* =================================================================================== *)

  (* will update the matrix in place *)
  let _add p i j phi = begin
    if debug then Debug.print "adding %s to (%s,%s) %s\n" (Info.string_of phi) (__t p i) (__t p j) (Info.string_of p.heap.(i).(j));
    assert( i <> j );
    assert( phi != p.heap.(i).(j) );
    Info.add ~org:p.heap.(i).(j) ~extra:phi;
    Info.update_diagonal p.heap.(j).(i) p.heap.(i).(j);

    if i = 0 || i = 1 (* nil or bottom *) then begin
      Info.kill_edges p.heap.(i).(j);
      Info.update_diagonal p.heap.(j).(i) p.heap.(i).(j);
    end;

    if j = 0 || j = 1 (* nil or bottom *) then begin
      Info.kill_edges p.heap.(j).(i);
      Info.update_diagonal p.heap.(i).(j) p.heap.(j).(i);
    end;

    if debug then Debug.print "\tbecame %s\n" (Info.string_of p.heap.(i).(j));
  end

  let _reset_label (p:t) x : unit = begin
    for i=0 to p.bound do Info.clear p.heap.(x).(i); Info.clear p.heap.(i).(x); done;
    Info.set p.heap.(x).(x) Info.Equal; (* Reset *)
  end

  let rec _split_and_free x acc p = begin
    try
      for z=0 to p.bound do (* Check if I have one guy eventually equal to x *)
	if x <> z && Info.is p.heap.(x).(z) Info.Equal then raise (Found z);
      done;
      
      (* no candidates, just remove x and forget that it was freed *)
      _reset_label p x;
      p.freecells.(x) <- false;
      p::acc

    with Found candidate -> begin 
      let tmp = ref [] in
      begin try
	let p1 = clone p in
	strengthen p1 candidate x Info.equal;
	p1.freecells.(candidate) <- true;
	p1.freecells.(x) <- false;
	_reset_label p1 x;
	tmp := [p1];
      with Inconsistent -> () end;
      let opt_p = try (* strengthening the original *) strengthen p candidate x Info.different; Some p with Inconsistent -> None in
      match opt_p with
      | None -> (* This constraint was impossible *) !tmp @ acc
      | Some p' -> _split_and_free x (!tmp @ acc) p'
    end
  end

  let _kill (p:t) x : t list = begin

    if p.freecells.(x) then begin 
      (* Passing the token to someone else *)
      try
	for z=0 to p.bound do (* Check if I have one guy for sure equal to x *)
	  if x <> z && Info.is_only p.heap.(x).(z) Info.Equal then raise (Found z);
	done;

	(* We haven't found anybody surely equal to x, we start the splitting *)
	_split_and_free x [] p

      with Found witness ->
	(* mark witness as free *)
	p.freecells.(witness) <- true;
	p.freecells.(x) <- false;
	_reset_label p x;
	[p]
    end else begin
      _reset_label p x;
      [p]
    end
  end


(* =================================================================================== *)

(* Must clone if necessary *)
  let equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    let x, y = index p thi lx, index p thi ly in
    if Info.is p.heap.(x).(y) Info.Equal then begin
      try
	let p' = clone p in
	strengthen p' x y Info.equal;	
	[p']
      with Inconsistent -> []
    end else []
  end

(* Must clone if necessary *)
  let non_equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    let x, y = index p thi lx, index p thi ly in

    if (* x =/= y *)
      Info.is p.heap.(x).(y) Info.Unrelated ||
      Info.is p.heap.(x).(y) Info.Reaches ||
      Info.is p.heap.(x).(y) Info.ReachesMore ||
      Info.is p.heap.(x).(y) Info.IsReached ||
      Info.is p.heap.(x).(y) Info.IsReachedMore
    then begin
      try
	let p' = clone p in
	strengthen p' x y Info.different;
	[p']
      with Inconsistent -> []
    end else []
  end

(* Must clone if necessary *)
  let next_equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x.next == y *)
    (* QUESTION: what to do if x.next is bottom. *)

    let x, y = index p thi lx, index p thi ly in
    check_dereferencing p thi x (sprintf "%s.next == %s" (Label.string_of lx) (Label.string_of ly));

    if (* x -> _ *) Info.is p.heap.(x).(index p thi Label.bottom) Info.Reaches then failwith("x.next == bottom");

    if Info.is p.heap.(x).(y) Info.Reaches then begin
      try
	let p' = clone p in
	strengthen p' x y (Info.create [Info.Reaches]); (* x -> y *)
	[p']
      with Inconsistent -> []
    end else []
  end

(* Must clone if necessary *)
  let non_next_equality (lx:Label.t) (ly:Label.t) p thi = begin
    (* x.next =/= y *)
    let x,y = index p thi lx, index p thi ly in
    check_dereferencing p thi x (sprintf "%s.next =/= %s" (Label.string_of lx) (Label.string_of ly));

    if Info.is_only p.heap.(x).(y) Info.Reaches then [] else begin
      try
	let p' = clone p in
	strengthen p' x y (Info.create [Info.Equal;Info.Unrelated;Info.ReachesMore;Info.IsReached;Info.IsReachedMore]); (* x -/-> y *)
	[p']
      with Inconsistent -> []
    end
  end


  let _assign p x y = begin
    if debug then Debug.print "_assign %s to %s\n" (__t p x) (__t p y);
    Info.set p.heap.(x).(y) Info.Equal; (* adding x = y *)

    (* Copying y *)
    for i=0 to p.bound do
      if i <> x then begin
	Info.reset p.heap.(i).(x) p.heap.(i).(y);
	Info.reset p.heap.(x).(i) p.heap.(y).(i); (* diagonal *)
      end;
    done;

    (* allocation *)
    (* We don't want to duplicate the information about the free status: if x==y and x is free, y will not be marked as free. It will be taken care of by _kill x *)
    (* p.freecells.(x) <- p.freecells.(y); *)
  end

(* No need to clone *)
  let assign (p:t) (thi:int) (lx:Label.t) (ly:Label.t) : t list = begin
    (* x := y *)
    let x,y = index p thi lx, index p thi ly in
    List.rev_map (fun p' -> _assign p' x y; p') (_kill p x)
  end


(* No need to clone *)
  let assign_dot_next (porg:t) (thi:int) (lx:Label.t) (ly:Label.t) : t list = begin
    (* x := y.next *)

      let x = index porg thi lx in

      let work acc p = begin
	try

          (* Adding the extra edges *)
	  let y = index p thi ly in
	  check_dereferencing p thi y (sprintf "%s := %s.next" (Label.string_of lx) (Label.string_of ly));
	
	  assert( x <> y );
	
	  let xisreachedbyy = Info.create [Info.IsReached] in (* x <- y *)
	  _add p x y xisreachedbyy;
      
	  for z=0 to p.bound do
	    if z <> x && z <> y then _add p x z (Info.merge xisreachedbyy p.heap.(y).(z));
	  done;
      
          (* Strengthening -- might raise Inconsistent *)
	  for u=0 to p.bound do
	    for v=0 to p.bound do
	      if u<>v && x<>u && x<>v then strengthen p x v (Info.merge p.heap.(x).(u) p.heap.(u).(v));
	      if u<>v && y<>u && y<>v then strengthen p y v (Info.merge p.heap.(y).(u) p.heap.(u).(v));
	    done;
	  done;

          (* Doesn't play with allocation anymore. *)
          (* x might be placed on a freed cell *)
	  (* so that sanity check would fail *)
	  (* Note that we still don't duplicate the information about the freed cell to x *)
	  p::acc
	with Inconsistent -> acc (* because it was raised at strenghthening *)
      end in
      List.fold_left work [] (_kill porg x)
  end

(* No need to clone *)
  let dot_next_assign (porg:t) (thi:int) (lx:Label.t) (ly:Label.t) : t list = begin
  (* x.next := y *)

    let x,y = index porg thi lx, index porg thi ly in
    check_dereferencing porg thi x (sprintf "%s.next := %s" (Label.string_of lx) (Label.string_of ly));
    assert( x <> y );

    if (* 0. Checking if we can get a loop *)
      Info.is porg.heap.(x).(y) Info.Equal ||
      Info.is porg.heap.(y).(x) Info.Reaches ||
      Info.is porg.heap.(y).(x) Info.ReachesMore
    then begin
      try
	strengthen (clone porg) y x (Info.create [Info.Equal]);
	strengthen (clone porg) y x (Info.create [Info.Reaches]);
	strengthen (clone porg) y x (Info.create [Info.ReachesMore]);
	print_trace porg "tmp/_debug/loop";
	raise (Insane (porg,(sprintf "LOOP!!! %s.next := %s" (__t porg x) (__t porg y))));
      with Inconsistent -> 
	strengthen porg y x (Info.create [Info.IsReached;Info.IsReachedMore;Info.Unrelated]);
	Debug.print "%s %s" Debug.yellow Debug.noColor;
    end;

    if (* 1. Checking if it is already an edge *)
      Info.is_only porg.heap.(x).(y) Info.Reaches
    then [porg] else begin


      (* Spitting the cases that reach x or not *)
      let reach =  Info.create [Info.Equal;Info.Reaches;Info.ReachesMore] in
      let notreach =  Info.create [Info.Unrelated;Info.IsReached;Info.IsReachedMore] in

      let apply i j c = begin
	if i=j 
	then [c] 
	else begin
	  if Info.should_split_edges c.heap.(i).(j) then begin
	    let tmp = ref [] in
	    begin try
	      let c1 = clone c in
	      strengthen c1 i j reach;
	      tmp := [c1];
	    with Inconsistent -> () end;
	    try
	      let c2 = clone c in
	      strengthen c2 i j notreach;
	      c2 :: !tmp
	    with Inconsistent -> !tmp
	  end else [c]
	end
      end in

      let res = ref [porg] in
      for i=0 to porg.bound do 
	res := List.fold_left (fun acc el -> acc @ (apply i x el)) [] !res;
      done;
     
      let do_the_job p = begin 
	
	let z'z = Info.create [Info.Unrelated] in
      
        (* 2.a Removing edges *)
	for z=0 to p.bound do
	  for z'=0 to p.bound do
	    if z <> z' && begin
	      (Info.is p.heap.(z').(x) Info.Reaches || Info.is p.heap.(z').(x) Info.ReachesMore) &&
	      (Info.is p.heap.(x).(z) Info.Reaches || Info.is p.heap.(x).(z) Info.ReachesMore) &&
	      (Info.is p.heap.(z').(z) Info.ReachesMore)
	    end || begin
	      (Info.is p.heap.(z').(x) Info.Equal) &&
	      (Info.is p.heap.(x).(z) Info.Reaches || Info.is p.heap.(x).(z) Info.ReachesMore) &&
	      (Info.is p.heap.(z').(z) Info.ReachesMore || Info.is p.heap.(z').(z) Info.Reaches)
	    end
	    then _add p z' z z'z;
	  done;
	done;
	
        (* 2.b Killing edges from x *)
	for z=0 to p.bound do
	  if x <> z then begin
	    if debug then Debug.print "Killing edge: %s to %s (from %s to " (__t p x) (__t p z) (Info.string_of p.heap.(x).(z));
	    Info.kill_edges p.heap.(x).(z);
	    Info.update_diagonal p.heap.(z).(x) p.heap.(x).(z);
	    if debug then Debug.print "%s)\n" (Info.string_of p.heap.(x).(z));
	  end;
	done;

        (* 2.c Propagation *)
	for z=0 to p.bound do
	  for z'=0 to p.bound do
	    if z <> z' && z <> x && z' <> x then strengthen p z' z (Info.merge p.heap.(z').(x) p.heap.(x).(z));
	  done;
	done;
	
        (* 3.a Adding back the edges *)
	if debug then Debug.print "Adding back the edges\n";
	Info.kill z'z Info.Unrelated; (* reusing the same object *)
	Info.set z'z Info.Reaches;
	Info.set z'z Info.ReachesMore;
	for z=0 to p.bound do
	  for z'=0 to p.bound do
	    if z <> z' && begin
	      (Info.is p.heap.(z').(x) Info.Equal || Info.is p.heap.(z').(x) Info.Reaches || Info.is p.heap.(z').(x) Info.ReachesMore) &&
	      (Info.is p.heap.(y).(z) Info.Equal || Info.is p.heap.(y).(z) Info.Reaches || Info.is p.heap.(y).(z) Info.ReachesMore)
	    end 
	    then _add p z' z z'z;
	  done;
	done;
	
        (* 3.b Sthrengthening *)
	Info.clear z'z; (* reusing the same object *)
	Info.set z'z Info.Reaches;
	strengthen p x y z'z;
	p
      end in
      
      List.fold_left (fun acc cons -> try (do_the_job cons)::acc with Inconsistent -> acc) [] !res
    end
  end

(* No need to clone *)
  let free_cell (p:t) (thi:int) (lx:Label.t) : t list = begin

    let x = index p thi lx in
    check_dereferencing p thi x (sprintf "free(%s)" (Label.string_of lx));
    (* TODO: raise an exception for double free *)
    p.freecells.(x) <- true;
    (* Make it point to _ *)
    dot_next_assign p thi lx Label.bottom
  end

(* No need to clone *)
  let make_new_cell (porg:t) (thi:int) (lx:Label.t) : t list = begin
    assert( Label.is_local lx );

    let x = index porg thi lx in

    let work acc p = begin

      assert( not(p.freecells.(x)) );

      (* Collecting the freed cells. Notice that one free might be equal to many other labels *)
      let freedvars = ref [] in
      for i=0 to p.bound do if p.freecells.(i) then freedvars := i :: !freedvars; done;

      assert(begin try
	List.iter (fun free1 -> begin 
	  List.iter (fun free2 -> begin 
	    if free1 <> free2 && Info.is p.heap.(free1).(free2) Info.Equal then raise Stop;
	  end) !freedvars;
	end) !freedvars; true with Stop -> false
      end);

      let reallocated = List.fold_left (fun accu free -> begin
	let p' = clone p in
	(* do x:=y on p' *)
	p'.freecells.(free) <- false;
	_assign p' x free;
	p'::accu
      end) [] !freedvars in

      (* Taking care of the cells going in many steps to bottom *)
      (* because they can go through a freed cell, without a label on it *)
      let candidates = ref [] in
      let iBottom = index p thi Label.bottom in
      let reaches = Info.create [Info.Reaches;Info.ReachesMore] in
      let reachesbottom = Info.create [Info.Reaches] in
      for z=0 to p.bound do
	if Info.is p.heap.(z).(iBottom) Info.ReachesMore then begin
	  assert( not(p.freecells.(z)) );
	  try
	    let p' = clone p in
	    for z'=0 to p.bound do
	      if z' <> x then _add p' z' x (Info.merge p'.heap.(z').(z) reaches(*z =>-> x*));
	    done;
	    _add p' x iBottom reaches; (* _add p' x iBottom (Info.merge p'.heap.(x).(iBottom) reaches); *)
	    strengthen p' x iBottom reachesbottom;
	    assert( not(p'.freecells.(z)) );
	    for z'=0 to p'.bound do if x <> z' then strengthen p' x z' Info.different; done;
	    candidates := p' :: !candidates;
	  with Inconsistent -> ()
	end;
      done;

      let forgottens = !candidates in

      (* Last one: I add a new cell, alone, with * color *)
      (* Make it reach anything that iBottom is equal to *)
      (* Notice that x is already reset *)
      for i=0 to p.bound do
	if i <> x then begin Info.set p.heap.(x).(i) Info.Unrelated; Info.set p.heap.(i).(x) Info.Unrelated; end;
      done;
      
      let isolated = dot_next_assign p thi lx Label.bottom in
      
      forgottens @ isolated @ reallocated @ acc

    end in
    List.fold_left work [] (_kill porg x)
  end

(* No need to clone *)
  let set_return_value (porg:t) (thi:int) (lx:Label.t) : t list = begin
  (* ret := x.data *)
    let x = index porg thi lx in
    check_dereferencing porg thi x (sprintf "ret := %s.data" (Label.string_of lx));

    let rec handle_color color acc p = begin
      if color < p.gvar+p.colors then begin
	assert( x <> color );
	let tmp = ref [] in
	begin try
	  let p1 = clone p in
	  strengthen p1 x color Info.equal;
	  p1.threads.(thi).return <- Data.reconstruct (color-p1.gvar,p1.translation.(color));
	  tmp := [p1];
	with Inconsistent -> () end;
	try
	  strengthen p x color Info.different;
	  handle_color (color+1) (!tmp @ acc) p
	with Inconsistent -> !tmp @ acc
	  (* handle_color (color+1) (!tmp @ acc) p *)

      end else begin
	(* Last color => It is neutral *)
	p.threads.(thi).return <- Data.neutral;
	p::acc
      end
    end in
    handle_color porg.gvar [] porg
  end

(* No need to clone *)
  let reset_return_value (p:t) (thi:int) : t list = begin
  (* ret := star  *)
    p.threads.(thi).return <- Data.top;
    [p]
  end

(* No need to clone *)
  let data_assign_var (p:t) (thi:int) (lx:Label.t) (ly:Label.t) : t list = begin
    failwith("Don't use it")
(*   (\* x.data := y *\) *)
(*   check_dereferencing p thi x; *)

(*   (\* CHEAT and MAKE IT STAR *\) *)
(*   [] *)
  end

(* No need to clone *)
  let init_thread p thi vars : t list = begin
    assert( p.threads.(thi).var = 0 );

    assert( try for i=0 to Array.length p.threads.(thi).bits - 1 do if p.threads.(thi).bits.(i) then raise Stop; done; true with Stop -> to_dot p "tmp/ouch"; false ); 

    let count = Array.length vars in
    let newBound = p.bound+count in
    let cut = begin
      let shift = ref 0 in
      for i=0 to p.nth - 1 do if i<thi then shift := p.threads.(i).var + !shift; done;
      p.gvar + p.colors + !shift
    end in
    
    let zero = Info.create [] in
    let h = Array.make_matrix (newBound+1) (newBound+1) zero in
    for i=0 to newBound do for j=0 to newBound do h.(i).(j) <- Info.clone zero; done; done;
    
    for i=0 to cut - 1 do
      for j=0 to cut - 1 do (* Copy the colors and globals *) Info.reset h.(i).(j) p.heap.(i).(j); done;
      for j=cut to p.bound do (* Taking care of the threads *) Info.reset h.(i).(j+count) p.heap.(i).(j); done;
    done;

    for i=cut to p.bound do
      for j=0 to cut - 1 do Info.reset h.(i+count).(j) p.heap.(i).(j); done;
      for j=cut to p.bound do Info.reset h.(i+count).(j+count) p.heap.(i).(j); done;
    done;

    let freecells = Array.make (newBound+1) false in
    for i=0 to cut - 1 do freecells.(i) <- p.freecells.(i); done;
    for i=cut to p.bound do freecells.(i+count) <- p.freecells.(i); done;
  (* between cut and cut+count-1, it's already false *)

    let trans = Array.make (newBound+1) "" in
    for i=0 to cut - 1 do trans.(i) <- p.translation.(i); done;
    for i=cut to p.bound do trans.(i+count) <- p.translation.(i); done;
    for i=0 to count - 1 do assert( i = Label.unpack vars.(i) ); trans.(cut+i) <- Label.string_of vars.(i); done;

    p.translation <- trans;
    p.bound <- newBound;
    p.heap <- h;
    p.freecells <- freecells;
    p.threads.(thi).var <- count;

    (* assign them to bottom *)
    let iBottom = index p thi Label.bottom in
    for i=cut to cut + count - 1 do
      Info.set h.(i).(i) Info.Equal;
      _assign p i iBottom;
    done;

    [p]
  end

(* No need to clone *)
  let kill_thread (porg:t) (thi:int) : t list = begin

    let vars = porg.threads.(thi).var in
    let newBound = porg.bound - vars in
    let zero = Info.create [] in
    let cut = begin
      let shift = ref 0 in
      for i=0 to porg.nth - 1 do if i<thi then shift := porg.threads.(i).var + !shift; done;
      porg.gvar + porg.colors + !shift
    end in

    (* TODO: when killing, move the token to another thread *)
    (* Note: it will probably not happen *)
    let work acc p = begin
      (* The variable are by construction killed *)

      let h = Array.make_matrix (newBound+1) (newBound+1) zero in
      for i=0 to newBound do for j=0 to newBound do h.(i).(j) <- Info.clone zero; done; done;

      (* Copying to the new heap. AFTER the label removing!! *)
      for i=0 to cut - 1 do
	for j=0 to cut - 1 do Info.reset h.(i).(j) p.heap.(i).(j); done;
	for j=cut to newBound do Info.reset h.(i).(j) p.heap.(i).(j+vars); done;
      done;
      for i=cut to newBound do
	for j=0 to cut - 1 do Info.reset h.(i).(j) p.heap.(i+vars).(j); done;
	for j=cut to newBound do Info.reset h.(i).(j) p.heap.(i+vars).(j+vars); done;
      done;
      
      (* Work on freecells and colors *)
      let freecells = Array.make (newBound+1) false in
      for i=0 to cut - 1 do freecells.(i) <- p.freecells.(i); done;
      for i=cut to newBound do freecells.(i) <- p.freecells.(i+vars); done;
      
      let trans = Array.make (newBound+1) "" in
      for i=0 to cut - 1 do trans.(i) <- p.translation.(i); done;
      for i=cut to newBound do trans.(i) <- p.translation.(i+vars); done;
      
      p.bound <- newBound;
      p.heap <- h;
      p.translation <- trans;
      p.freecells <- freecells;
      _reset_thread p.threads.(thi);
      
      p::acc
    end in

    let todo = ref [porg] in
    for i=cut to cut + vars-1 do
      todo := List.fold_left (fun acc p -> acc @ (_kill p i)) [] !todo;
    done;

    List.fold_left work [] !todo
  end

  let concretize_data p thi lv data = begin
    if Data.is_interesting data then begin
      let v = index p thi lv in
      let color = p.gvar + Data.unpack data in
      (* assigning the color to v *)
      List.rev_map (fun p' -> _assign p' color v; p') (_kill p color)
    end else [p]
  end

(* Must clone when needed *)
  let validate_insert (porg:t) (thi:int) (var:Label.t) (all: (Observer.data * Observer.state) list ) : t list  = begin
    List.fold_left (fun acc (data_,s) -> match data_ with
    | Observer.NoData | Observer.State _ ->  failwith("that's a weird observer transition")
    | Observer.ObsData data -> begin
	match promise porg thi with
	| Promise.Insert dlist ->
	    List.fold_left (fun acc' d -> if Data.equal data d then begin
	      let p = clone porg in
	      set_observer p s;
	      reset_promise p thi;
	      (concretize_data p thi var d) @ acc
	    end else acc') acc dlist
	| _ -> acc (* wrong promise *)
    end) [] all
  end

(* Must clone when needed *)
  let validate_delete (porg:t) (thi:int) (all: (Observer.data * Observer.state) list ) : t list  = begin
    List.fold_left (fun acc (data,s) -> match data with
    | Observer.NoData | Observer.State _ ->  failwith("that's a weird observer transition")
    | Observer.ObsData d -> begin
	if Data.compatible porg.threads.(thi).return d then begin
	  let p = clone porg in
	(* p.threads.(thi).return <- d; *)
	  set_observer p s;
	  reset_promise p thi;
	  p::acc
	end else acc (* wrong promise *)
    end) [] all
  end

(* Must clone when needed *)
  let validate_empty (porg:t) (thi:int) (all: (Observer.data * Observer.state) list ) : t list  = begin
    List.fold_left (fun acc (data,s) -> match data with
    | Observer.ObsData _ | Observer.NoData ->  failwith("that's a weird observer transition")
    | Observer.State s' -> begin
	match promise porg thi with
	| Promise.ReturnEmpty obs when Observer.same_state obs s' ->
	    let p = clone porg in
	    set_observer p s;
	    reset_promise p thi;
	    p::acc
	| _ -> acc (* not the right promise: DIE !!! *)
    end) [] all
  end

(* Must clone when needed *)
  let main_lock porg thi lock = begin
    (* assert( not(porg.lockstates.(lock).(thi)) ); (\* we don't want to lock again *\) *)
    let locked = ref false in
    for t=0 to porg.nth - 1 do if porg.lockstates.(lock).(t) then locked := true; done;
    if !locked then [] else begin
      let p = clone porg in
      p.lockstates.(lock).(thi) <- true;
      [p]
    end
  end

  let main_unlock porg thi lock = begin
    assert( porg.lockstates.(lock).(thi) ); (* we don't want to unlock a free lock *)
    let p = clone porg in
    p.lockstates.(lock).(thi) <- false;
    [p]
  end

(* =================================================================================== *)


  let swap (porg:t) : t = begin
    assert( porg.nth = 2 );
    let p = clone porg in
    let gbound = porg.gvar + porg.colors in
    let pbound = porg.bound in
    let th0var = porg.threads.(0).var in
    let th1var = porg.threads.(1).var in

    (* swapping the threads *)
    p.threads.(0) <- porg.threads.(1);
    p.threads.(1) <- porg.threads.(0);

    (* Exchanging position for th0 and th1 *)
    for i=gbound + th0var to pbound do p.freecells.(i-th0var) <- porg.freecells.(i); done;
    for i=gbound to gbound + th0var - 1 do p.freecells.(i+th1var) <- porg.freecells.(i); done;

    for i=gbound + th0var to pbound do p.translation.(i-th0var) <- porg.translation.(i); done;
    for i=gbound to gbound + th0var - 1 do p.translation.(i+th1var) <- porg.translation.(i); done;

    (* For the heap now *)
    for i=0 to gbound - 1 do
      for j=gbound + th0var to pbound do p.heap.(i).(j-th0var) <- porg.heap.(i).(j) done;
      for j=gbound to gbound + th0var - 1 do p.heap.(i).(j+th1var) <- porg.heap.(i).(j) done;
    done;

    for i=gbound + th0var to pbound do
      for j=0 to gbound - 1 do p.heap.(i-th0var).(j) <- porg.heap.(i).(j) done;
      for j=gbound + th0var to pbound do p.heap.(i-th0var).(j-th0var) <- porg.heap.(i).(j) done;
      for j=gbound to gbound + th0var - 1 do p.heap.(i-th0var).(j+th1var) <- porg.heap.(i).(j) done;
    done;

    for i=gbound to gbound + th0var - 1 do
      for j=0 to gbound - 1 do p.heap.(i+th1var).(j) <- porg.heap.(i).(j) done;
      for j=gbound + th0var to pbound do p.heap.(i+th1var).(j-th0var) <- porg.heap.(i).(j) done;
      for j=gbound to gbound + th0var - 1 do p.heap.(i+th1var).(j+th1var) <- porg.heap.(i).(j) done;
    done;

    (* For the locks *)
    for lock=0 to p.locks do
      p.lockstates.(lock).(0) <- porg.lockstates.(lock).(1);
      p.lockstates.(lock).(1) <- porg.lockstates.(lock).(0);
    done;

    p
  end

  let sanitize p = begin

(*     let lukas (i,j) = (i=0 || j=0) && Info.is_only p.heap.(i).(j) Info.Equal in *)

    (* ============================================================== *)
    (* ==============     Big cheat for keep part of     ============ *)
    (* ==============     the heap in the signature      ============ *)
    (* ============================================================== *)
    let n = Label.local (2,"next'") and pcs = [104;105] in
(*     let fred (i,j) = (i=0 || j=0) && Info.is_only p.heap.(i).(j) Info.Equal in *)
    let rec fred = function
      | 0,j ->
	  (List.exists ((=) p.threads.(0).pc) pcs && (j = index p 0 n) && Info.is_only p.heap.(0).(j) Info.Equal) ||
	  (List.exists ((=) p.threads.(1).pc) pcs && (j = index p 1 n) && Info.is_only p.heap.(0).(j) Info.Equal)
      | i,0 -> fred (0,i) | _ -> false in
    let lukas = if p.gvar > 3 then fred else (fun _ -> false) in
    (* ============================================================== *)

    assert( is_sane p ); (* assert( if is_sane p then true else (to_dot p "tmp/bad"; false) ); *)

    let string_of_freecell str fc = sprintf "%s%s" !str (if fc then "T" else "F") in
    let string_of_thread str th = sprintf "%s%s%d|" !str (encode_thread th) th.var in
    let string_of_lock str lockstate = sprintf "%s%s|" !str (if lockstate then "L" else "_") in
    let string_of_cell str cell = sprintf "%s%s|" !str (Info.string_of cell) in
    let info = sprintf "%s-%d-%d-%d-%d-" (Observer.string_of_state (observer p)) p.nth p.bound p.gvar p.colors in
    let encode = sprintf "%s.%s.%s.%s.%s." in

    let threads1 = let str = ref "" in for i=0 to p.nth - 1 do str := string_of_thread str p.threads.(i); done; !str in
    let allocation1 = let str = ref "" in for i=0 to p.bound do str := string_of_freecell str p.freecells.(i); done; !str in
    let locks1 =  let str = ref "" in for lock=0 to p.locks do for t=0 to p.nth-1 do str := string_of_lock str p.lockstates.(lock).(t); done; str := !str ^ "#"; done; !str in
    let global1 = let str = ref "" in for i=0 to p.bound do for j=0 to p.bound do if lukas (i,j) then str:=string_of_cell str p.heap.(i).(j);done;str:=(!str)^"#";done; !str in
    let encoding1 = encode info threads1 allocation1 locks1 global1 in

    let p' = swap p in
    let threads2 = let str = ref "" in for i=0 to p'.nth - 1 do str := string_of_thread str p'.threads.(i); done; !str in
    let allocation2 = let str = ref "" in for i=0 to p'.bound do str := string_of_freecell str p'.freecells.(i); done; !str in
    let locks2 =  let str=ref "" in for lock=0 to p'.locks do for t=0 to p'.nth-1 do str := string_of_lock str p'.lockstates.(lock).(t); done; str := !str ^ "#"; done; !str in
    let global2 = let str=ref "" in for i=0 to p'.bound do for j=0 to p'.bound do if lukas (i,j) then str:=string_of_cell str p'.heap.(i).(j);done;str:=(!str)^"#";done; !str in
    let encoding2 = encode info threads2 allocation2 locks2 global2 in

    if encoding1 < encoding2 then
      p.encoding <- encoding1
    else begin
      p.encoding <- encoding2;
      p.heap <- p'.heap;
      p.threads <- p'.threads;
      p.lockstates <- p'.lockstates;
      p.translation <- p'.translation;
      p.freecells <- p'.freecells;
    end
  end

  let post_process ?(sanitizing=true) p = begin
    if sanitizing then sanitize p;
    [p]
  end

(* =================================================================================== *)

  type key = string
  let key p = p.encoding
  let string_of_key k = k
  let join_hash k = Hashtbl.hash k
  let join_equal = (=)

  let debugJOIN = false
  let join ~org ~extra : bool = begin
    let changed = ref false in
    let where = ref (-1,-1) in

    if debug || debugJOIN then to_dot org (sprintf "tmp/_debug/%d-joined-with-%d--1-org" (id org) (id extra));

    for i=0 to org.bound do
      for j=0 to org.bound do
	if Info.join ~org:org.heap.(i).(j) ~extra:extra.heap.(i).(j) then (if !changed = false then where := (i,j); changed := true;);
      done;
    done;
    if !changed then begin
      log org (sprintf "Joined with %d -- the first change was at (%d,%d)" (id extra) (fst !where) (snd !where));
      if debug || debugJOIN then begin
	to_dot org (sprintf "tmp/_debug/%d-joined-with-%d--3-res" (id org) (id extra));
	to_dot extra (sprintf "tmp/_debug/%d-joined-with-%d--2-extra" (id org) (id extra));
      end;
    end;
    !changed
  end

(* =================================================================================== *)

  let reset_counter p position = Array.iter (fun th -> if th.pc <> 0 then th.bits.(position) <- false;) p.threads
  let is_uptodate p thi position = p.threads.(thi).bits.(position)
  let make_uptodate p thi position = p.threads.(thi).bits.(position) <- true

(* =================================================================================== *)

  let create_queue nth (head:Label.t) (tail:Label.t) colors bits locks = begin

    assert( 2 = Label.unpack head && 3 = Label.unpack tail );
    let c = create nth [|head;tail|] colors bits locks in

(*     to_dot c "tmp/init"; *)

    let iNull = index c (-1) Label.nil in
    let iHead = index c (-1) head in
    let iTail = index c (-1) tail in

    Info.clear c.heap.(iHead).(iNull);
    Info.clear c.heap.(iNull).(iHead);
    Info.clear c.heap.(iTail).(iNull);
    Info.clear c.heap.(iNull).(iTail);
    Info.clear c.heap.(iHead).(iTail);
    Info.clear c.heap.(iTail).(iHead);

    let reach = Info.create [Info.Reaches] in

    _add c iHead iNull reach;
    _add c iTail iNull reach;

    Info.set c.heap.(iHead).(iTail) Info.Equal;
    Info.set c.heap.(iTail).(iHead) Info.Equal;

    sanitize c;
(*     to_dot c "tmp/init2"; *)
    [c]

(*     let c' = create nth [|head;tail|] colors bits in *)

(*     let iNull' = index c' (-1) Label.nil in *)
(*     let iHead' = index c' (-1) head in *)
(*     let iTail' = index c' (-1) tail in *)
    
(*     c'.heap.(iHead').(iTail') <- Reach; *)
(*     c'.heap.(iTail').(iNull') <- OneStep; *)

(*     c'.heap.(iHead').(iHead') <- Equal; *)
(*     c'.heap.(iTail').(iTail') <- Equal; *)

(*     sanitize c'; *)

(*     [c;c'] *)
  end

  let create_stack nth (top:Label.t) colors bits locks = begin

    assert( 2 = Label.unpack top );
    let c = create nth [|top|] colors bits locks in

(*     let iNull = index c (-1) Label.nil in *)
(*     let iTop = index c (-1) top in *)
    
(*     Info.set c.heap.(iTop).(iNull) Info.Equal; *)
(*     Info.set c.heap.(iNull).(iTop) Info.Equal; *)
(*     Info.set c.heap.(iTop).(iTop) Info.Equal; *)
(*     sanitize c; *)
(*     [c] *)

    let res = assign c (-1) top Label.nil in
    List.iter sanitize res;
    res
  end

(* let create_empty_buckets _ _ = [] *)

  let fake _ = begin
    
    let h = Array.make_matrix 4 4 (Info.create []) in
    for i=0 to 3 do for j=0 to 3 do h.(i).(j) <- Info.clone h.(i).(j); done; done;
    for i=0 to 3 do Info.set h.(i).(i) Info.Equal done;
    let freecells = Array.make 4 false in
    let c = {
      nth = 2;
      threads = Array.init 2 (fun _ -> thread_create 0);
      heap = h;
      freecells=freecells;
      gvar = 2;
      colors = 0;
      bound = 3;
      lockstates = (Array.make_matrix 0 2 false);
      locks=(-1);

      encoding=""; (* to be sanitized *)
      
      translation = [|"#";"S";"t";"x";|];

      id = 0;
      messages = [];
      alive = true;
      in_queue=false;
      observer = Observer.init;
      parent = None;
    } in

    c.threads.(0).var <- 2;
    c.threads.(0).pc <- 110;
    c.threads.(0).return <- Data.neutral;

    Info.set c.heap.(0).(1) Info.IsReachedMore;
    Info.set c.heap.(0).(2) Info.IsReached;
    Info.set c.heap.(0).(2) Info.IsReachedMore;
    Info.set c.heap.(0).(3) Info.IsReached;
    Info.set c.heap.(0).(3) Info.IsReachedMore;

    Info.set c.heap.(1).(2) Info.IsReached;
    Info.set c.heap.(1).(2) Info.Reaches;

    Info.set c.heap.(1).(3) Info.Equal;
    Info.set c.heap.(1).(3) Info.Reaches;

    Info.set c.heap.(2).(3) Info.Equal;
    Info.set c.heap.(2).(3) Info.Reaches;
    Info.set c.heap.(2).(3) Info.IsReached;

    for i=0 to 3 do
      for j=i+1 to 3 do
	Info.update_diagonal c.heap.(j).(i) c.heap.(i).(j);
      done;
    done;
    
    sanitize c;

(*     Debug.print "Checking consistency\n"; *)
(*     _check_consistency (0,1) c; *)

    Debug.print "Strengthening\n";
    
    strengthen c 0 2 (Info.create [Info.IsReachedMore]);

    c
  end

let view _ _ = failwith("not implemented")
let build_key _ = failwith("not implemented")
let extend _ _ _ = failwith("not implemented")
let trim _ = failwith("not implemented")
let is_more_general _ _ = failwith("not implemented")

end (* !module Joined *)
