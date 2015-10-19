let sprintf = Printf.sprintf
let debug = false
(* ========================================================================================================= *)
(* =====================                        Constraint                          ======================== *)
(* ========================================================================================================= *)

module Implementation : Constraint.C = struct
let name = "Graph"

let debugSanitize = false
let debugSanitizeDeep = false
let debugEncoding = false
let debugEncodingDeep = false

module H = Heap
module Vertex = H.Vertex
module LS = Heap.LS
module LT = Heap.LT

exception Stop

(* Global counter, for identification *)  
let maxID = ref (-1)
    
(* ====================================================================================================== *)
(* =====================                        Threads                          ======================== *)
(* ====================================================================================================== *)

module Thread = struct
  type t = {
      mutable pc: int;
      mutable promise: Promise.t;
      mutable return: Data.t;
      mutable locals: (LS.t * bool) array;
      mutable l2n: int LT.t;
      mutable encoding: string;
      mutable must_sanitize: bool;
      mutable nopost: bool;
      mutable bits: bool array;
    } 
  let create nvertex b = {
    pc=0; promise=Promise.NoPromise; locals=Array.make nvertex (LS.empty,false); encoding=""; l2n=LT.create 0; must_sanitize=true; nopost=false; return=Data.top;
    bits = (Array.make b false);
  }
  let clone th = { th with locals = Array.copy th.locals;
		   l2n=LT.copy th.l2n; 
		   bits = Array.copy th.bits; (* the remainder will be copied *)}

  let to_dot th = 
    sprintf "PC: %d     Promise: %s   Return: %s   Bits:[|%s]%s%s"
      th.pc (Promise.string_of th.promise) (Data.string_of th.return) (Array.fold_left (sprintf "%s%B|") "" th.bits)
      (if debug then "\\n1-Encoding: "^th.encoding else "") (if th.must_sanitize then "\\nmust sanitize" else "")

  let string_of th = sprintf "%s PC:%d, Promise:%s" (if th.must_sanitize then "(must sanitize)" else "") th.pc (Promise.string_of th.promise)
  let info th =
    sprintf "%d-%s-%s-%s"
      th.pc (Promise.string_of th.promise) (Data.string_of th.return) (Array.fold_left (sprintf "%s,%B") "" th.bits)


  let must_sanitize th = th.must_sanitize
  let make_sanitizable th = th.must_sanitize <- true

  let pc th = th.pc
  let set_pc th pc = th.pc <- pc
  let promise th = th.promise
  let set_promise th prom = th.promise <- prom
  let reset_promise th = make_sanitizable th; th.promise <- Promise.NoPromise
  let reset_return th = th.return <- Data.top

  let bit th i = th.bits.(i)
  let set_bit th i b = make_sanitizable th; th.bits.(i) <- b

  let encoding th = th.encoding
  let set_encoding th e = th.must_sanitize <- false; th.encoding <- e
      
  let add_label th label node = begin
    assert( not(Label.is_global label) );
    let locals, flag = th.locals.(node) in
    assert( not(LS.mem label locals) );
    th.locals.(node) <- LS.add label locals, flag;
    assert( not(LT.mem th.l2n label) );
    LT.add th.l2n label node;
    make_sanitizable th;
  end
      
  let remove_label th label node = begin
    assert( not(Label.is_global label) );
    let node = LT.find th.l2n label in
    let locals, flag = th.locals.(node) in
    assert( LS.mem label locals );
    th.locals.(node) <- LS.remove label locals, flag;
    LT.remove th.l2n label;
    make_sanitizable th;
  end

  let update_color node b th = th.locals.(node) <- fst th.locals.(node), b

  let locals th = Array.map fst th.locals
  let color_updates th = Array.map (fun (_,uptodate) -> if uptodate then "Y" else "N") th.locals
  let string_of_locals th thi node = LS.fold (fun label acc -> sprintf "%s,%s.%d" acc (Label.string_of label) thi) (fst th.locals.(node))
  let has_no_locals th node = LS.is_empty (fst th.locals.(node))

  let add_vertex th = make_sanitizable th; th.locals <- Array.append th.locals [|(LS.empty,false)|]
      
  let get_node th label = LT.find th.l2n label

  let reset th = begin
    LT.clear th.l2n;
    Array.iteri (fun i _ -> th.locals.(i) <- LS.empty,false ;) th.locals;
    reset_promise th;
    reset_return th;
    for i=0 to Array.length th.bits - 1 do th.bits.(i) <- false done;
    make_sanitizable th;
  end

  let get_return th = th.return
  let set_return th r = th.return <- r

end

module Classes = Hashtbl.Make(struct type t = string let hash = Hashtbl.hash let equal = (=) end)
module LSi = Set.Make(struct type t = Label.t * int let compare (l1,i1) (l2,i2) = let c = Pervasives.compare i1 i2 in if c <> 0 then c else Label.compare l1 l2 end)

type t = {

    heap: H.t;
    mutable nth:int;
    mutable threads: Thread.t array;

    id:int;
    mutable messages:string list;
    mutable alive: bool;
    mutable observer: Observer.state;      (** The state of the observer *)
    mutable parent: t option;
    mutable children: t list;
    mutable encoding: string; (* the minimal word given all permutations of the threads *)
    mutable classes: int list Classes.t;
    mutable minperms: int list list;
    mutable minshape: string;
  } 

(* must reencode afterwards *)
let create nth b = incr maxID;
  let threads = Array.init nth (fun _ -> Thread.create 2 b) in (* just 2 vertices: nil and bottom, with b bits *)
  let classes = Classes.create nth in
  let rec threads_list curr limit acc = if curr=limit then acc else threads_list (curr+1) limit (curr::acc) in
  Classes.add classes "" (threads_list 0 nth []);
  { id = (!maxID);
    nth = nth;
    threads = threads;
    heap = H.create ();
    messages = [];
    alive = true;
    observer = Observer.init;
    parent = None;
    children = [];
    encoding = "";
    classes = classes;
    minperms = [];
    minshape = "";
  }
    
let clone t = assert( t.alive ); incr maxID;
  { t with id=(!maxID);
    threads = Array.map Thread.clone t.threads;
    heap = H.clone t.heap;
    classes = Classes.copy t.classes;
    (* will copy the rest *) 
  }
let light_clone t =
  assert( t.alive ); incr maxID;
  { t with id=(!maxID);
    threads = Array.map Thread.clone t.threads;
    classes = Classes.copy t.classes;
    (* same shape *)
  }

let string_of t =
  sprintf "%s[Observer=%s%s]"
    (if t.alive then "" else "(deleted)")
    (Observer.string_of_state t.observer)
    (Array.fold_left (fun acc th -> sprintf "%s%s|" acc (Thread.info th)) "|" t.threads)

(* ========================================================================================================= *)
(* =====================                        Printing                            ======================== *)
(* ========================================================================================================= *)

let to_dot (p:t) (where:string) = begin

  let info = begin
    let generator = 
      let format s = (Str.global_substitute (Str.regexp "\n") (fun s -> "\\n") s) in
      fst (List.fold_right (fun s (acc,i) -> sprintf "--------------- %d ---------------\\n%s\\n%s" i (format s) acc, i+1) p.messages ("",1))
    in
    sprintf "%sObserver: %s\\nParent: %s\\nEncoding: %s\\nMin-shape: %s\\nMin-perms: %s\\n\\n%s"
      (if p.alive then "" else "Deleted\\n")
      (Observer.string_of_state p.observer)
      (match p.parent with None -> "orphelin" | Some papa -> string_of_int papa.id)
      p.encoding
      p.minshape
      (List.fold_left (fun acc perms -> sprintf "%s,[%s]" acc (List.fold_left (sprintf "%s,%d") "" perms)) "" p.minperms)
      generator
  end in
  let threads = ref "subgraph threads {label=\"\";\n" in
  Array.iteri (fun thi th -> threads := sprintf "%sth%d [shape=box;label=\"Th:%d     %s\"];\n" !threads thi thi (Thread.to_dot th)) p.threads;
  threads := !threads ^ "}\n";
  let heap = ref "" in
  let get_locals node = 
    let locals = ref "" in
    Array.iteri (fun i th -> locals := Thread.string_of_locals th i node !locals) p.threads;
    !locals
  in
  H.iter_vertex p.heap (fun src v -> begin
    heap := !heap ^ (Vertex.to_dot v src (get_locals src));
    if src <> H.vnil && src <> H.vbottom then heap := sprintf "%s%d -> %d [color=blue];\n" !heap src (H.succ p.heap src);
  end);

  let res = sprintf "digraph G {rankdir=LR;\nlabel=\"%s\";\n%s\n%s\n}" info !threads !heap in
  let oc = open_out (where ^ ".dot") in Printf.fprintf oc "%s" res; close_out oc;
end

(* ========================================================================================================= *)
(* =====================                        Utilities                           ======================== *)
(* ========================================================================================================= *)

let id t = t.id
let observer t = t.observer
let set_observer t obs = t.observer <- obs
    
let log t message = t.messages <- message::t.messages

let nthreads p = p.nth

let is_alive t = t.alive
let delete t = t.alive <- false

let set_parent p p' = p.parent <- Some p'
let parent p = match p.parent with None -> failwith("no parent") | Some papa -> papa

let pc p thi = Thread.pc p.threads.(thi)  
let set_pc p thi pc = Thread.set_pc p.threads.(thi) pc  

let promise p thi = Thread.promise p.threads.(thi)  
let set_promise p thi prom = Thread.set_promise p.threads.(thi) prom
let reset_promise p thi = Thread.reset_promise p.threads.(thi)

let get_return_value p thi = Thread.get_return p.threads.(thi)
let set_return_value p thi = Thread.set_return p.threads.(thi)

let rec iter_trace p f = begin
  f p;
  match p.parent with
  | Some papa when papa != p (*physically*) -> iter_trace papa f
  | _ -> ()
end

let print_trace p where = iter_trace p (fun p' -> to_dot p' (sprintf "%s-%d" where p'.id))

let vbottom p = H.get p.heap H.vbottom
and vnil p = H.get p.heap H.vnil
and is_nil v = v = H.vnil
and is_bottom v = v = H.vbottom
and nil = H.vnil
and bottom = H.vbottom

let lambda (cons:t) thi (label:Label.t) : int = begin
  if Label.is_global label
  then H.get_node cons.heap label
  else Thread.get_node cons.threads.(thi) label
end

let succ (cons:t) v : int = H.succ cons.heap v

let update_data p thi vid = begin
  (* I assume for the moment that there is only one parameter passed to the push *)
  Vertex.set_data (H.get p.heap vid) (Data.top);
  (* update the color_update for that thread, and kill the others *)
  Array.iteri (fun thid th -> Thread.update_color vid (thid=thi) th) p.threads;
end

let concretize_data p thi var data = begin
  let vid = lambda p thi var in
  Vertex.set_data (H.get p.heap vid) data;
  (* kill all updates *)
  Array.iter (Thread.update_color vid false) p.threads;
end

let get_data p (vid:int) : Data.t = Vertex.get_data (H.get p.heap vid)

let has_cycle p = H.has_cycle p.heap
    
let add_vertex (p:t) : int = begin
  let v = Vertex.empty () in
  Array.iter Thread.add_vertex p.threads;
  H.add_vertex p.heap v
end (* must recompute the 1-encoding *)
    
let redirect_edge p = begin
  Array.iter Thread.make_sanitizable p.threads;
  H.redirect_edge p.heap
end
    
let add_vertex_in_edge p vFrom vTo = begin
  let vid = add_vertex p in
  H.add_edge p.heap vid vTo;
  H.redirect_edge p.heap vFrom vid;
  vid
end
    
let add_label p thi vid (label:Label.t) = begin
  if Label.is_global label
  then (Array.iter Thread.make_sanitizable p.threads; H.add_label p.heap vid label)
  else Thread.add_label p.threads.(thi) label vid
end

let remove_label p thi vid label = begin
  if Label.is_global label
  then (Array.iter Thread.make_sanitizable p.threads; H.remove_label p.heap vid label)
  else Thread.remove_label p.threads.(thi) label vid
end

let clean (p:t) : unit = begin
  let cleaned = ref false in
  let can_be_cleaned vid = Array.fold_left (fun acc th -> acc && (Thread.has_no_locals th vid)) true p.threads in
  let c = ref true in
  while !c do
    c := false;
    H.iter_vertex p.heap (fun vid v -> begin
      match can_be_cleaned vid, Vertex.is_cleanable v with
      |	true, true -> (* no labels and white *)
(* 	  if Vertex.is_simple v then begin *)
	  cleaned := true; c := true;
	  H.clean_vertex p.heap vid v;
(* 	  end else if has_no_locals (succ p vid) then begin *)
(* 	    cleaned := true; c := true; *)
(* 	    H.clean_vertex p.heap vid v; *)
(* 	  end; *)

      |	true, false when Vertex.is_leaf v -> (* no labels and red or blue *) begin
	  cleaned := true; c := true;
	  H.clean_vertex p.heap vid v;
      end
(*       |	true, false when Vertex.is_simple v -> (\* no labels and red or blue *\) begin *)
(* 	  match Vertex.preds v with *)
(* 	  | [pred] -> *)
(* 	      let vpred = get p.heap pred in *)
(* 	      cleaned := true; c := true; *)
(* 	      H.clean_vertex p.heap vid v; *)
(* 	  | _ -> failwith("impossible") *)
(*       end *)
      |	_ -> ()
    end);
  done;
  if !cleaned then Array.iter Thread.make_sanitizable p.threads;
end

let reset_thread (p:t) thi : unit = begin
  Thread.reset p.threads.(thi);
  clean p;
end (* must recompute the 1-encoding *)

(* ========================================================================================================= *)
(* =====================                       Entailement                          ======================== *)
(* ========================================================================================================= *)

let hash p = Hashtbl.hash p.encoding
let compare p1 p2 = String.compare p1.encoding p2.encoding
let equal p1 p2 = p1.encoding = p2.encoding

let _compute cons : unit = begin

  if debugEncoding then Debug.print "Preparing the encoding for %s\n" (string_of cons);

  let get_shape cons threads : string = begin
    let locals = Array.make (H.nb_vertex cons.heap) LSi.empty in
    let updates = Array.make (H.nb_vertex cons.heap) "" in
    Array.iteri (fun thi th -> begin
      assert( not(Thread.must_sanitize th) );
      Array.iteri (fun vid labels -> locals.(vid) <- LSi.union locals.(vid) (LS.fold (fun label acc -> LSi.add (label,thi) acc) labels LSi.empty)) (Thread.locals th);
      Array.iteri (fun vid update -> updates.(vid) <- updates.(vid) ^ update) (Thread.color_updates th);
    end) threads;
    let string_of_pairs labels = LSi.fold (fun (label,i) acc -> sprintf "%s,%s.%d" acc (Label.string_of label) i) labels "" in
    let arr = Array.map string_of_pairs locals in
    Array.iteri (fun vid str -> arr.(vid) <- str ^ updates.(vid)) arr;
    H.encode cons.heap arr
  end in
  (* Get the equivalence classes in order *)
  let classes = Classes.fold (fun word ths acc -> (word,ths)::acc) cons.classes [] in
  let ordered_classes = List.fast_sort (fun (a,_) (b,_) -> H.order a b) classes in
  let flips = List.map (fun (_,ths) -> Utils.permute ths) ordered_classes in
  (* combining the flips per class into a big permutation *)
  let rec get_permutations accu = function
    | [] -> failwith("shouldn't come here")
    | [permutations] -> permutations
    | permutations::tail ->
	let all = get_permutations [] tail in
	List.fold_left (fun acc perm -> List.fold_left (fun acc' permu -> (perm @ permu) :: acc') acc all) [] permutations
  in
  (* I need to try all the valid permutations for the n threads and pick the smallest *)
  let permutations = get_permutations [] flips in
  if debugEncoding then begin
    Debug.print "I found those permutations:\n";
    Debug.level (1);
    List.iter (fun perm -> Debug.print "[%s]\n" (List.fold_left (sprintf "%s,%d") "" perm);) permutations;
    Debug.print "out of those classes:\n";
    Debug.level (1);
    List.iter (fun (word,ths) -> Debug.print "%s -> %s\n" word (List.fold_left (sprintf "%s,%d") "" ths)) classes;
    Debug.level (-2);
  end;
  match permutations with
  | [] -> failwith("impossible permutations?")
  | head::tail ->

      (* fix the first encoding *)
      let threads = Array.copy cons.threads in
      let length = Array.length cons.threads in
      let index = ref 0 in
      List.iter (fun thi -> threads.(!index) <- cons.threads.(thi); incr index;) head;
      assert( !index = length );

      let shape = get_shape cons threads in
      cons.minperms <- [head];
      cons.minshape <- shape;

      (* get the smallest one among the others *)
      List.iter (fun perms -> begin
	index := 0;
	List.iter (fun thi -> threads.(!index) <- cons.threads.(thi); incr index;) perms;
	assert( !index = length );
	let curr = get_shape cons threads in
	match H.order curr cons.minshape with
	| comp when comp < 0 -> (* I found a strictly smaller shape *)
	    cons.minperms <- [perms];
	    cons.minshape <- curr;
	| comp when comp = 0 -> (* I found another minimal shape *)
	    cons.minperms <- perms::cons.minperms;
	| _ -> () (* This permutation does not generate a smaller shape-word *)
      end) tail;

end

let _encode cons : unit = begin

  if debugEncoding then Debug.print "Encoding %s\n" (string_of cons);

  let get_info cons threads : string = Array.fold_left (fun acc th -> sprintf "%s|%s" acc (Thread.info th)) "" threads in

  match cons.minperms with
  | [] -> failwith("impossible")
  | head::tail ->
      
      let threads = Array.copy cons.threads in
      let length = Array.length cons.threads in
      let index = ref 0 in
      let min_ordered_ths = ref head in
      List.iter (fun thi -> threads.(!index) <- cons.threads.(thi); incr index;) head;
      assert( !index = length );
      cons.encoding <- cons.minshape ^ (get_info cons threads);
      
      List.iter (fun perms -> begin
	index := 0;
	List.iter (fun thi -> threads.(!index) <- cons.threads.(thi); incr index;) perms;
	assert( !index = length );
	let curr = cons.minshape ^ (get_info cons threads) in
	if H.order curr cons.encoding < 0 then begin
	  cons.encoding <- curr;
	  min_ordered_ths := perms;
	end;
      end) tail;

      (* making a minperms the order for the threads *)
      index := 0;
      List.iter (fun thi -> threads.(!index) <- cons.threads.(thi); incr index;) !min_ordered_ths;
      cons.threads <- threads;
end

(* let _compute cons : unit = begin *)

(*   if debugEncoding then Debug.print "Preparing the encoding for %s\n" (string_of cons); *)

(*   let get_shape cons threads : string = begin *)
(*     let locals = Array.make (H.nb_vertex cons.heap) LSi.empty in *)
(*     let updates = Array.make (H.nb_vertex cons.heap) "" in *)
(*     Array.iteri (fun thi th -> begin *)
(*       assert( not(Thread.must_sanitize th) ); *)
(*       Array.iteri (fun vid labels -> locals.(vid) <- LSi.union locals.(vid) (LS.fold (fun label acc -> LSi.add (label,thi) acc) labels LSi.empty)) (Thread.locals th); *)
(*       Array.iteri (fun vid update -> updates.(vid) <- updates.(vid) ^ update) (Thread.color_updates th); *)
(*     end) threads; *)
(*     let string_of_pairs labels = LSi.fold (fun (label,i) acc -> sprintf "%s,%s.%d" acc (Label.string_of label) i) labels "" in *)
(*     let arr = Array.map string_of_pairs locals in *)
(*     Array.iteri (fun vid str -> arr.(vid) <- str ^ updates.(vid)) arr; *)
(*     H.encode cons.heap arr *)
(*   end in *)
(*   let shape = get_shape cons cons.threads in *)
(*   cons.minshape <- shape; *)
(* end *)

(* let _encode cons : unit = begin *)

(*   if debugEncoding then Debug.print "Encoding %s\n" (string_of cons); *)

(*   let get_info cons threads : string = Array.fold_left (fun acc th -> sprintf "%s|%s" acc (Thread.info th)) "" threads in *)

(*   cons.encoding <- cons.minshape ^ (get_info cons cons.threads); *)
(* end *)

(* Recomputes the 1-encoding for every thread *)
let _sanitize cons force : unit = begin
  if debugSanitize then Debug.print "Sanitizing %s\n" (string_of cons);
  assert( H.check cons.heap );

  let add_to_class enc thi = begin
    let _all = try Some (Classes.find cons.classes enc) with Not_found -> None in
    match _all with
    | Some all -> assert( not(List.mem thi all) );
	Classes.replace cons.classes enc (thi::all)
    | None ->
	Classes.add cons.classes enc [thi]
  end in

  let must_reencode = ref false in
  Classes.clear cons.classes;
  Array.iteri (fun thi th -> begin
    let encoding =
      if Thread.must_sanitize th then begin
	must_reencode := true;
	let locals = Array.map H.string_of_labels (Thread.locals th) in
	let encoding' = H.encode cons.heap locals in (* I don't encode the pc,prom,stack in the 1-world view *)
	Thread.set_encoding th encoding';
	encoding'
      end else Thread.encoding th
    in
    add_to_class encoding thi;
  end) cons.threads;
  (* Note: this updates the equivalence classes too *)
  if debugSanitize then begin
    Debug.print "Classes:\n";
    Debug.level (1);
    Classes.iter (fun k v -> Debug.print "[%s] in class: %s\n" (List.fold_left (sprintf "%s,%d") "" v) k) cons.classes;
    Debug.level (-1);
    Debug.print "--------\n";
  end;
  
  if debugEncoding then Debug.print "Must reencode after sanitizing\n";
  if !must_reencode || force then _compute cons;
  _encode cons;
  if debugEncoding then Debug.print "=> Encoding: %s\n" cons.encoding;
  
end

  let sanitize  cons = begin
(* let sanitize cons : unit = begin *)
  _sanitize cons true;
(*   _compute cons; *)
(*   _encode cons; *)
end

  let post_process ?(sanitizing=true) p = begin
    if sanitizing then sanitize p;
    [p]
  end

(* =================================================================================== *)
exception NullPointerDereferencing of t * string
exception DoubleFree of t * string
exception Dangling of t * string
exception ClashWithInit of t

let check_dereferencing p v str = begin
  if is_nil v then raise (NullPointerDereferencing (p,str));
  if is_bottom v then raise (Dangling (p,str));
end

let make_new_cell porg thi x = begin
  assert( Label.is_local x );

  (* remove the label x *)
  remove_label porg thi (lambda porg thi x) x;

  (* Add a deallocated cell, that will play the role of the newly inserted cell *)
  let p = clone porg in
  let nnew = add_vertex p in (* it is allocated, and all threads are sanitizable *)
  add_label p thi nnew x;
  H.add_edge p.heap nnew H.vbottom;
  Vertex.set_data (H.get p.heap nnew) Data.top;
  (* the color updates are all false *)
  
  (* foreach deallocated cell, clone, allocate the cell and put x on it *)
  H.fold_vertex porg.heap [p] (fun acc vid v -> if Vertex.is_deallocated v then begin
    assert( not(is_nil vid) && not(is_bottom vid) );
    let p' = clone porg in
    add_label p' thi vid x;
    Vertex.allocate v;
    (* sanitize p'; *)
    Array.iter Thread.make_sanitizable p'.threads;
    
    update_data p' thi vid; (* cheating *)
    
    p'::acc
  end else acc)
end

let free_cell p thi x = begin
  assert( Label.is_local x ); 
  let vid = lambda p thi x in
  assert( not(is_nil vid) && not(is_bottom vid) );
  let v = H.get p.heap vid in
  Vertex.deallocate v;
  Array.iter Thread.make_sanitizable p.threads;
(*       redirect_edge p vx (P.vbottom p); *)
(*       clean p; *)
  [p]
end

let equality x y p thi = begin
  let vx,vy = lambda p thi x, lambda p thi y in
  if vx = vy 
  then [clone p]
  else []
end

let non_equality x y p thi = begin
  let vx,vy = lambda p thi x, lambda p thi y in
  if vx <> vy
  then [clone p]
  else []
end

let next_equality x y p thi = begin
  let vx = lambda p thi x in
  check_dereferencing p vx (sprintf "%s.next == %s" (Label.string_of x) (Label.string_of y));
  let vnext = succ p vx in
  let vy = lambda p thi y in
  if vnext = vy then [clone p] else []
end

let non_next_equality x y p thi = begin
  let vx = lambda p thi x in
  check_dereferencing p vx (sprintf "%s.next =/= %s" (Label.string_of x) (Label.string_of y));
    (* some imprecision here *)
  [clone p]
end
    
let assign p thi x y = begin
  let vx,vy = lambda p thi x, lambda p thi y in
  if vx = vy then [p] else begin
    remove_label p thi vx x;
    add_label p thi vy x;
    clean p;
    [p]
  end
end

let reset_counter p position = Array.iter (fun th -> if Thread.pc th <> 0 then Thread.set_bit th position false;) p.threads
let is_uptodate p thi position = Thread.bit p.threads.(thi) position
let make_uptodate p thi position = Thread.set_bit p.threads.(thi) position true
    
let data_assign_var p thi x y = begin
  let vx = lambda p thi x in
  check_dereferencing p vx ((Label.string_of x) ^ ".data := " ^ (Label.string_of y));
  update_data p thi vx; (* P.set_data p thi vx y; *)
  clean p;
  [p]
end

let set_return_value p thi y = begin
  let vy = lambda p thi y in
  check_dereferencing p vy ("ret := " ^ (Label.string_of y) ^ ".data");
  set_return_value p thi (get_data p vy);
  [p]
end

(* No need to clone *)
  let reset_return_value (p:t) (thi:int) : t list = begin
  (* ret := star  *)
    Thread.reset_return p.threads.(thi);
    [p]
  end


let assign_dot_next p thi x y = begin
  let vx,vy = lambda p thi x, lambda p thi y in
  check_dereferencing p vy ((Label.string_of x) ^ " := " ^ (Label.string_of y) ^ ".next");
  remove_label p thi vx x;
  let vnext = succ p vy in
  
  let p' = clone p in
  add_label p' thi vnext x;
  clean p';
  
  let vid = add_vertex_in_edge p vy vnext in
  add_label p thi vid x;
  clean p;
  
  [p;p']
end

let dot_next_assign p thi x y = begin
  let vx,vy = lambda p thi x, lambda p thi y in
  check_dereferencing p vx ((Label.string_of x) ^ ".next := " ^ (Label.string_of y));
  redirect_edge p vx vy;
  clean p;
  [p]
end

let init_thread p thi vars = begin
  Array.iter (fun x -> add_label p thi bottom x;) vars;
    (* Thread.init_bits p.threads.(thi) bits; *)
  [p]
end

let kill_thread p thi = begin
  reset_thread p thi;
  clean p;
  [p]
end

let validate_empty porg thi obs_data = begin
  List.fold_left (fun acc (data,s) -> match data with
  | Observer.ObsData _ | Observer.NoData ->  failwith("that's a weird observer transition")
  | Observer.State s' -> begin
      let p = clone porg in
      match promise p thi with
      | Promise.ReturnEmpty obs when Observer.same_state obs s' ->
	  set_observer p s;
	  reset_promise p thi;
	  p::acc
      | _ -> acc (* not the right promise: DIE !!! *)
  end) [] obs_data
end

let validate_insert porg thi var obs_data = begin
  List.fold_left (fun acc (data_,s) -> match data_ with
  | Observer.NoData | Observer.State _ ->  failwith("that's a weird observer transition")
  | Observer.ObsData data -> begin
      match promise porg thi with
      | Promise.Insert dlist ->
	  List.fold_left (fun acc' d -> if Data.equal data d then begin
	    let p = clone porg in
	    set_observer p s;
	    concretize_data p thi var data;
	    reset_promise p thi;
	    p::acc
	  end else acc') acc dlist
      | _ -> acc (* wrong promise *)
  end) [] obs_data
end

let validate_delete porg thi obs_data = begin
  List.fold_left (fun acc (data,s) -> match data with
  | Observer.NoData | Observer.State _ ->  failwith("that's a weird observer transition")
  | Observer.ObsData d -> begin
      let d' = get_return_value porg thi in
      if Data.compatible d d' then begin
	let p = clone porg in
	set_observer p s;
	reset_promise p thi;
	p::acc
      end else acc (* wrong promise *)
  end) [] obs_data
end



(* =================================================================================== *)

let create_queue nth (head:Label.t) (tail:Label.t) (colors:Data.t array) bits _ = begin
  let c = create nth bits in
  let vid = add_vertex c in
  add_label c (-1) vid head;
  add_label c (-1) vid tail;
  H.add_edge c.heap vid H.vnil;
  sanitize c;
  [c]
end

let create_stack nth (top:Label.t) (colors:Data.t array) bits _ = begin
  let c = create nth bits in
  add_label c (-1) H.vnil top;
  sanitize c;
  [c]
end

  (* let create_empty_buckets _ _ = [] *)

  type key = unit
  let key _ = failwith("not implemented")
  let string_of_key _ = failwith("not implemented")
  let join_hash _ = failwith("not implemented")
  let join_equal _ _ = failwith("not implemented")
  let join ~org ~extra = failwith("not implemented")
  let fake _ = failwith("not implemented")
      
  let main_lock _ _ _ = failwith("not implemented")
  let main_unlock _ _ _ = failwith("not implemented")

  let set_in_queue _ _ = failwith("not implemented")
  let in_queue _ = failwith("not implemented")
  let set_in_slice _ _ = failwith("not implemented")
  let in_slice _ = failwith("not implemented")

  let view _ _ = failwith("not implemented")
  let build_key _ = failwith("not implemented")
  let extend _ _ _ = failwith("not implemented")
  let trim _ = failwith("not implemented")
  let is_sane _ = failwith("not implemented")
  let is_more_general _ _ = failwith("not implemented")
end
