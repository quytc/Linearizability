let sprintf = Printf.sprintf 

let debug = false
let debugClean = false

module LT = Hashtbl.Make(struct type t = Label.t let hash = Hashtbl.hash let equal = (=) end)
module LS = Set.Make(Label)
let string_of_labels labels = LS.fold (fun el acc -> sprintf "%s,%s" (Label.string_of el) acc) labels ""

module Vertex = struct

  type t = {
      mutable allocation: bool;
      mutable data: Data.t;
      mutable globals: LS.t;
      mutable preds: int list;
      mutable succ: int option;
      mutable in_cycle: bool;
      mutable cleaned: bool;
    }

  let create globals alloc d = { globals=globals; data=d; allocation=alloc; preds=[]; succ=None; in_cycle=false; cleaned=false; }
  let empty _ = create LS.empty true Data.neutral
  let clone v = { v with data=v.data; (* will copy the rest*) }

  let string_of v = begin sprintf "{ %s | %s | %s | Children:%s | Parent:%s }"
      (string_of_labels v.globals) (Data.string_of v.data) (match v.allocation with | true -> "" | false -> "free")
      (List.fold_left (sprintf "%s,%d") "" v.preds) (match v.succ with None -> "none" | Some p -> string_of_int p)
  end   

  let to_dot v id locals = begin
    let text,shape = 
      if LS.mem Label.nil v.globals || LS.mem Label.bottom v.globals
      then sprintf "%s%s" (string_of_labels v.globals) locals, "ellipse"
      else sprintf "{%s%s%s}" (string_of_labels v.globals) locals (if v.allocation then "" else " | ✘"), "Mrecord"
    in
    let color = if v.allocation then "black" else "red" in
    sprintf "%d [label=\"%s\",shape=%s,style=filled,color=\"%s\",fillcolor=\"%s\"];\n" id text shape color (if v.cleaned then "black" else Data.color (Data.string_of v.data))
  end
      
  let add_label v label = begin
    assert( Label.is_global label );
    v.globals <- LS.add label v.globals
  end

  let remove_label v label = begin
    assert( Label.is_global label );
    v.globals <- LS.remove label v.globals
  end
      
  let is_simple v = List.length v.preds < 2
  (* it is assumed that this function is called if no locals are on that vertex *)      
  let is_cleanable v = LS.is_empty v.globals && Data.is_cleanable v.data
  let clean v = (* assert( is_cleanable v ); *) v.cleaned <- true
  let is_not_cleaned v = not(v.cleaned)

  let get_data v = v.data
  let set_data v data = v.data <- data
  let reset_data v = v.data <- Data.top

  let deallocate v : unit = assert( v.allocation ); v.allocation <- false
  let allocate v : unit = assert( not(v.allocation) ); v.allocation <- true
  let allocation v = v.allocation
  let is_deallocated v : bool = not(v.allocation)

  let preds v = v.preds
  let remove_pred n v = v.preds <- List.filter ((<>) n) v.preds
  let add_pred n v = v.preds <- n::v.preds

  let succ v = v.succ
  let set_succ p v = v.succ <- Some p

  let reset v = v.in_cycle <- false
  let mark v = v.in_cycle <- true
  let cycle v = v.in_cycle

  let encode locals v = begin
    sprintf "<%s-%s-%s-%s>" (string_of_labels v.globals) (Data.string_of v.data) (if v.allocation then "A" else "D") locals
  end

  let is_leaf v = LS.is_empty v.globals && match v.preds with [] -> true | _ -> false

  let get_gvars v = LS.fold (fun el acc -> (el,-1)::acc) v.globals []
end

let vnil = 0 (* the tree rooted at Nil *)
let vbottom = 1 (* the tree rooted at Bottom *)
type cycle = int array (* the cycle is stored as parent <- child *)

type t = {
    mutable vertices: Vertex.t array;
    globals: int LT.t;
    mutable cycles: int array;   (** lists of cycles. *)
  } 

type vertex = Vertex.t

let create _ = begin
  let vn = Vertex.create (LS.singleton Label.nil) true Data.neutral in
  let vb = Vertex.create (LS.singleton Label.bottom) true Data.neutral in
  let h = [|vn;vb|] in
  let globals = LT.create 4 in
  LT.add globals Label.nil vnil;
  LT.add globals Label.bottom vbottom;
  { vertices=h; globals = globals; cycles = [||]; }
end

let clone h =
  let vertices = Array.copy h.vertices in
  Array.iteri (fun i v -> vertices.(i) <- Vertex.clone v) h.vertices;
  { vertices = vertices;
    globals = LT.copy h.globals;
    cycles = Array.copy h.cycles;
  }

let get h n = h.vertices.(n)

let get_node h label = assert( Label.is_global label ); LT.find h.globals label

let succ h v = begin
  assert( v <> vnil && v <> vbottom );
  match Vertex.succ (get h v) with
  | None -> failwith("shouldn't be asking such questions...")
  | Some next -> next
end
    
exception Cycle
 
let has_cycle h = begin
  let module S = Set.Make(struct type t = int let compare = Pervasives.compare end) in
  let rec inspect acc node = begin
    match Vertex.succ (get h node) with
    | None when (node = vnil || node = vbottom) -> ()
    | None -> failwith("can reach anywhere");
    | Some next when S.mem next acc -> raise Cycle;
    | Some next -> inspect (S.add node acc) next
  end in
  try Array.iteri (fun i _ -> inspect (S.singleton i) i) h.vertices; false
  with Cycle -> true
end
    
(* ========================================================================================================= *)
(* =====================                        Utilities                           ======================== *)
(* ========================================================================================================= *)

let nb_vertex h = Array.length h.vertices
let iter_vertex h f = Array.iteri (fun vid v -> if Vertex.is_not_cleaned v then f vid v;) h.vertices
let fold_vertex h init f = let acc = ref init in Array.iteri (fun i v -> if Vertex.is_not_cleaned v then acc := f !acc i v) h.vertices; !acc

let add_label h vid label = begin
  assert( Label.is_global label );
  Vertex.add_label (get h vid) label;
  assert ( not(LT.mem h.globals label) );
  LT.add h.globals label vid
end  

let remove_label h vid label = begin
  assert( Label.is_global label );
  Vertex.remove_label (get h vid) label;
  assert ( LT.mem h.globals label );
  LT.remove h.globals label
end  

let add_vertex h v = begin
  h.vertices <- Array.append h.vertices [|v|];
  Array.length h.vertices - 1
end

(* the src should not point anywhere *)
let add_edge h src dst = begin
  let vsrc, vdst = get h src, get h dst in
  assert( (match Vertex.succ vsrc with None -> true | _ -> false) );
  Vertex.set_succ dst vsrc;
  assert( not(List.exists ((=) src) (Vertex.preds vdst)) );
  Vertex.add_pred src vdst;
end

let redirect_edge (cons:t) src dst = begin
  assert( not(has_cycle cons) );
  assert( src <> vnil && src <> vbottom );

  let vsrc, vdst = get cons src, get cons dst in
  let succ = match Vertex.succ vsrc with None -> failwith("impossible") | Some p -> p in 

  if succ <> dst then begin
    let vnext = get cons succ in
    Vertex.remove_pred src vnext;
    Vertex.set_succ dst vsrc;
    Vertex.add_pred src vdst;

    (* TODO: Check for cycles *)
(*     if not(Vertex.cycle vdst) then begin *)
(*       let rec can_reach n visited = begin *)
(* 	match Vertex.succ (get cons n) with *)
(* 	| None when n = vnil || n = vbottom -> false *)
(* 	| None -> failwith("can reach anywhere") *)
(* 	| Some next when List.mem next visited -> true *)
(* 	| Some next -> can_reach next (n::visited) *)
(*       end in if can_reach dst [src] then failwith("I created a cycle"); *)
(*     end *)
(*     else if Vertex.cycle vsrc then begin *)
(*       (\* nothing to do, I make it point inside a*\) *)
(*     end *)
  end
end


(* let add_vertex_in_edge cons src dst = begin *)
(*   assert( src <> vnil && src <> vbottom ); *)
(*   let vsrc,vdst = get cons src, get cons dst in *)
(*   let v = Vertex.empty () in *)
(*   Vertex.set_succ dst v; *)
(*   Vertex.add_pred src v; *)
(*   let n = add_vertex cons v in *)
(*   Vertex.remove_pred src vdst; *)
(*   Vertex.add_pred n vdst; *)
(*   Vertex.set_succ n vsrc; *)
(*   (\* TODO: if the edge was in a cycle, update the latter *\) *)
(*   n *)
(* end *)

let clean_vertex h vid v = begin
  Vertex.clean v;
  let dst = succ h vid in
  let vdst = get h dst in
  Vertex.remove_pred vid vdst;
  List.iter (fun predid -> Vertex.add_pred predid vdst; Vertex.set_succ dst (get h predid)) (Vertex.preds v);
end

(* ========================================================================================================= *)
(* =====================                        Encoding                            ======================== *)
(* ========================================================================================================= *)

let order (a:string) (b:string) : int = begin
  String.compare a b (* I hope it is the lexicographic ordering *)
end

(* Depth-First Search *)
let rec dfs h f n = begin
  let v = get h n in assert( Vertex.is_not_cleaned v );
  let children = List.map (dfs h f) (Vertex.preds v) in
  let ordered_children = List.sort order children in
  let children_encoding = List.fold_left (^) "" ordered_children in
  sprintf "%s[%s]" (f (n,v)) children_encoding
end

(* locals is an array of string, representing the encodings of local variables on that vertex id *)
let encode h locals = begin
  sprintf "%s|%s"
    (dfs h (fun (n,v) -> Vertex.encode locals.(n) v) vbottom)
    (dfs h (fun (n,v) -> Vertex.encode locals.(n) v) vnil)
end

let check h : bool = begin
  let alright = ref true in
  iter_vertex h (fun vid v -> begin
    match Vertex.succ v with
    | None -> ()
    | Some next -> 
	let vnext = get h next in
	if not(List.mem vid (Vertex.preds vnext)) then begin
	  Debug.print "Shape problem: %d is not a child of %d, or %d not its successor" vid next next;
	  alright := false;
	end;
  end;);
  !alright
end
