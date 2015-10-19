let sprintf = Printf.sprintf

module type P_Sig = sig

  type p
  exception InconsistentExn
  module V : sig
    type t
    val equal: t -> t -> bool
    val compare: t -> t -> int
    val string_of: t -> string
    val has_globals: t -> bool
    val equal_data: t -> t -> bool
    val is_dirty: t -> bool
    val is_dirty_and_colored: t -> bool
    val make_dirty: t -> unit
    val must_local: t -> bool
    val make_local: t -> unit
    val is_eventually_deallocated: t -> bool
    val is_deallocated: t -> bool
    val make_allocated: t -> unit
    val make_deallocated: t -> unit
  end
  type vertex = V.t
  type edge = Label.Edge.t
  module E : sig
    val anti: edge -> edge
    val string_of: vertex -> vertex -> edge -> string
  end
 
  val are_explicitly_not_equal: p -> vertex -> vertex -> bool
  val get_vertex: p -> Label.t -> vertex
  val find_vertex: p -> vertex -> vertex
  val get_succ: p -> vertex -> vertex option
  val is_inconsistent: ?force:bool -> p -> bool
  val clean: p -> unit
  val to_dot: p -> string -> unit
  val vbottom: p -> vertex
  val vnil: p -> vertex
  val log_message: p -> string -> unit
  val string_of: p -> string
  val id: p -> int
      
  val add_vertex: p -> vertex -> unit
  val remove_vertex: p -> vertex -> unit
  val mem_edge: p -> vertex -> vertex -> edge -> bool
  val add_edge: p -> vertex -> vertex -> edge -> bool

  val remove_edge: p -> vertex -> vertex -> edge -> unit
  val iter_vertex: p -> (vertex -> unit) -> unit

  val iter_edges: p -> (vertex -> vertex -> edge -> unit) -> unit
  val iter_edge: p -> edge -> (vertex -> vertex -> unit) -> unit
  val succ: p -> vertex -> edge -> vertex list
  val pred: p -> vertex -> edge -> vertex list
  val iter_succ: p -> vertex -> edge -> (vertex -> unit) -> unit
  val iter_pred: p -> vertex -> edge -> (vertex -> unit) -> unit

  val clone: p -> p
  val get_cycle: p -> vertex -> edge -> vertex list
  val merge_vertices: p -> remove:vertex -> replace:vertex -> unit
  val make_not_equal: p -> vertex -> vertex -> bool
end

module type Sat_sig = sig
  type elt
  val apply: elt -> elt list
  val apply_next: elt -> Label.t -> Label.t -> elt list
end

module Make (P : P_Sig) : Sat_sig with type elt = P.p
      = 
  struct
    
    type p = P.p
    type elt = p
    exception Inconsistent = P.InconsistentExn
    module Vertex = P.V
    module Edge = P.E
    type vertex = Vertex.t
    type edge = Label.Edge.t
    open Label.Edge

    let debugSaturation = Debug.saturation
    let debugSaturationDeep = Debug.saturation_deep
    let debugNextSaturation = Debug.next_saturation
    let debugNextSaturationDeep = Debug.next_saturation_deep
    let saturationSleeping = false


    type predicate = 
	Reachability | NonReachability | ImmediateReachability | NonImmediateReachability |
	Difference | Equality |
	Reachability' | NonReachability' | ImmediateReachability' | NonImmediateReachability' |
	Locality |
	Allocation

    let string_of_predicate = function
      | Reachability -> "Reachability" | Reachability' -> "Colored Reachability"
      | NonReachability -> "Non Reachability" | NonReachability' -> "Colored Non Reachability"
      | ImmediateReachability -> "Immediate Reachability" | ImmediateReachability' -> "Colored Immediate Reachability"
      | NonImmediateReachability -> "Non Immediate Reachability" | NonImmediateReachability' -> "Colored Non Immediate Reachability"
      | Equality -> "It has merged some vertices"
      | Difference -> "Difference"
      | Locality -> "Locality/Globality"
      |	Allocation -> "Allocation"

    module PS = struct
      module S = Set.Make(struct type t = predicate let compare = Pervasives.compare end)
      include S
      let edge_to_predicate = function
	| Reachable -> Reachability
	| ReachableInTheNew -> Reachability'
	| NotReachable -> NonReachability
	| NotReachableInTheNew -> NonReachability'
	| OneStepReachable -> ImmediateReachability
	| NotOneStepReachable -> NonImmediateReachability
	| OneStepReachableInTheNew -> ImmediateReachability'
	| NotOneStepReachableInTheNew -> NonImmediateReachability'
	| _ ->failwith("eh?")
      let from e = singleton (edge_to_predicate e) 
      let add_from e s = add (edge_to_predicate e) s
      let string_of s = fold (fun el acc -> sprintf "%s,%s" acc (string_of_predicate el)) s ""
    end

    exception Branching of (elt * PS.t) list
    exception Reloop
    exception Stop

    let print_branching_with bList = Debug.print "Branching with [%s]\n" (List.fold_left (fun acc (el,_) -> sprintf "%s%d|" acc (P.id el)) "|" bList)

(* 2. two terms behaving (one step reachable, reachable) in opposite ways with respect to some Label.t are different *)
    let induce_differenciation p = begin
      let has_changed = ref false in
      P.iter_edges p (fun src dst e ->
	List.iter (fun v' -> if P.make_not_equal p src v' && not(!has_changed) then has_changed := true;) 
	  (match e with
	  | OneStepReachable -> P.pred p dst NotOneStepReachable
	  | OneStepReachableInTheNew -> P.pred p dst NotOneStepReachableInTheNew
	  | Reachable -> P.pred p dst NotReachable
	  | ReachableInTheNew -> P.pred p dst NotReachableInTheNew
	  | _ -> []);
	);
      if !has_changed then PS.singleton Difference else PS.empty
    end

(* 2.1: differenciate with locality *)
    let differenciate_with_locality p = begin
      let has_changed = ref false in
      P.iter_vertex p (fun x -> 
	if Vertex.must_local x then begin
	  P.iter_vertex p (fun y ->
	    if Vertex.is_dirty y then begin
	      if P.make_not_equal p x y then has_changed := true;
	    end;);
	end;
	);
      if !has_changed then PS.singleton Difference else PS.empty
    end

(* 3.1: self reachability (first parameter: Reachable | ReachableInTheNew)*)
    let self_reachability etype p = begin
      let has_changed = ref false in
      P.iter_vertex p (fun n -> if P.add_edge p n n etype && not(!has_changed) then has_changed := true;);
      if !has_changed then PS.from etype else PS.empty
    end

(* 3.2: make it reachable in several steps *)
(* 4: reachability transitivity *)
    let complete_reachability_positive porg = begin
      let changes = ref PS.empty in
      let rec complete_reachability_rec p must_loop = begin
	P.iter_edges p (fun src dst e -> match e with
	| OneStepReachable -> if P.add_edge p src dst Reachable then (must_loop := true; changes := PS.add_from Reachable !changes;);
	| OneStepReachableInTheNew -> if P.add_edge p src dst ReachableInTheNew then (must_loop := true; changes := PS.add_from ReachableInTheNew !changes; ); 
	| Reachable -> P.iter_succ p dst Reachable (fun dst' ->if P.add_edge p src dst' Reachable then (must_loop := true; changes := PS.add_from Reachable !changes; ); )
	| ReachableInTheNew -> P.iter_succ p dst ReachableInTheNew (fun dst' ->
	    if P.add_edge p src dst' ReachableInTheNew then (must_loop := true; changes := PS.add_from ReachableInTheNew !changes; );)
	| _ -> ());
	if !must_loop then complete_reachability_rec p (ref false);
      end in
      complete_reachability_rec porg (ref false);
      !changes
    end

(* 3.3: make it different *)
(* 3.4: make it not one step reachable *)
(* e = NotReachable && e' = NotOneStepReachable or same thing in the new *)
    let complete_reachability_negative e e' porg = begin
      let changes = ref PS.empty in
      let rec complete_reachability_rec p must_loop = begin
	P.iter_edge p e (fun src dst ->
	  if P.add_edge p src dst e' then (must_loop := true; changes := PS.add_from e' !changes; );
	  if P.make_not_equal p src dst then (must_loop := true; changes := PS.add Difference !changes; );
	  );
	if !must_loop then complete_reachability_rec p (ref false);
      end in
      complete_reachability_rec porg (ref false);
      !changes
    end

    let identify_one_reachable e porg = begin
      let has_changed = ref false in
      let rec identify_one_reachable_rec p = begin
	try 
	  P.iter_vertex p (fun v ->
	    match P.succ p v e with
	    | [] -> () | [v1] -> ()
	    | v1::others -> List.iter (fun v' -> P.merge_vertices p v' v1; (* v' disappears *)) others; raise Reloop;
		);
	with Reloop -> has_changed := true; identify_one_reachable_rec p;
      end in
      identify_one_reachable_rec porg;
      if !has_changed then PS.singleton Equality else PS.empty
    end

(* share: in an scc, terms one step reaching some Label.t form a singleton *)
    let share_reachability immreach reach porg = begin
      let has_changed = ref false in
      let rec share_reachability_rec p = begin
	try
	  P.iter_edge p immreach (fun x z -> P.iter_pred p z immreach (fun y -> 
	    if not(Vertex.equal x y) && P.mem_edge p x y reach && P.mem_edge p y x reach then ( P.merge_vertices p x y; raise Reloop; ); 
	    ););
	with Reloop -> has_changed:=true; share_reachability_rec p
      end in
      share_reachability_rec porg;
      if !has_changed then PS.singleton Equality else PS.empty
    end

(* 10.1, 10.2: propagating non reachability *)
    let propagating_non_reachability notreach reach porg = begin
      let has_changed = ref false in
      let rec propagating_non_reachability_rec p must_loop = begin
	P.iter_edge p notreach (fun x z ->
	  assert( not(Vertex.equal x z) );
	  P.iter_succ p x reach (fun y -> assert( not(Vertex.equal y z) ); if P.add_edge p y z notreach then must_loop := true;);
	  P.iter_pred p z reach (fun y -> assert( not(Vertex.equal x y) ); if P.add_edge p x y notreach then must_loop := true;);
	  );
	if !must_loop then ( has_changed := true; propagating_non_reachability_rec p (ref false); );
      end in
      propagating_non_reachability_rec porg (ref false);
      if !has_changed then PS.from notreach else PS.empty
    end

(* propagating scc reachability *)
    let propagating_scc_reachability notreach reach porg = begin
      let has_changed = ref false in
      let rec propagating_scc_reachability_rec p must_loop = begin
	P.iter_edge p notreach (fun y z ->
	  if P.mem_edge p z y notreach then
	    P.iter_pred p y reach (fun x -> if P.add_edge p x z notreach then must_loop := true;);
	  );
	if !must_loop then ( has_changed := true; propagating_scc_reachability_rec p (ref false); );
      end in
      propagating_scc_reachability_rec porg (ref false);
      if !has_changed then PS.from notreach else PS.empty
    end

(* propagating non one reachability *)
    let propagating_non_one_reachability notimmreach immreach p = begin
      let has_changed = ref false in
      P.iter_edge p Different (fun y z ->
	assert( P.mem_edge p z y Different );
	P.iter_pred p y immreach (fun x -> if P.add_edge p x z notimmreach then has_changed := true;);
	);
      if !has_changed then PS.from notimmreach else PS.empty
    end

    let stepping reach notimmreach p = begin
      let has_changed = ref false in
      P.iter_edge p reach (fun x y ->
	if not(Vertex.equal x y) then begin
	  P.iter_succ p y reach (fun z ->
	  if not(Vertex.equal z y) && not(Vertex.equal z x) then begin
	    if P.add_edge p x z notimmreach then has_changed := true;
	  end;);
	end;);
      if !has_changed then PS.from notimmreach else PS.empty
    end

    let propagate_globality_from_global_labels p = begin
      let has_changed = ref false in
      P.iter_vertex p (fun v ->
	if Vertex.has_globals v then begin
	  if not( Vertex.is_dirty v ) then ( Vertex.make_dirty v; has_changed := true; );
	end;
	);
      if !has_changed then PS.singleton Locality else PS.empty
    end

(*  propagate globality *)
    let propagate_globality reach p = begin
      let has_changed = ref false in
      P.iter_vertex p (fun x ->
	if Vertex.is_dirty x then begin
	  P.iter_succ p x reach (fun y ->
	    if Vertex.must_local y then ( if debugSaturation then P.log_message p "propagate globality -> inconsistent"; raise Inconsistent; );
	    if not( Vertex.is_dirty y ) then ( Vertex.make_dirty y; has_changed := true;);
	    );
	end;);
      if !has_changed then PS.singleton Locality else PS.empty
    end

(* propagate globality *)
    let non_reachability_with_globality notreach p = begin
      let has_changed = ref false in
      P.iter_vertex p (fun v -> if Vertex.is_dirty v then P.iter_vertex p (fun v' -> if Vertex.must_local v' && P.add_edge p v v' notreach then has_changed := true;););
      if !has_changed then PS.from notreach else PS.empty
    end


(* 13.1: propagate locality. *)
(* 13.2: already implemented in 12.1 *)
    let propagate_locality reach p = begin
      let has_changed = ref false in
      P.iter_edge p reach (fun x y ->
	if Vertex.must_local y then begin
	  if Vertex.is_dirty x then ( if debugSaturation then P.log_message p "propagate locality"; raise Inconsistent; );
	  if not( Vertex.must_local x ) then ( Vertex.make_local x; has_changed := true; );
	end;
	);
      if !has_changed then PS.singleton Locality else PS.empty
    end

    let resolve_data_difference p = begin
      let has_changed = ref false in
      P.iter_vertex p (fun v1 -> P.iter_vertex p (fun v2 ->
	if not(Vertex.equal v1 v2) && not(Vertex.equal_data v1 v2) then begin 
	  if P.make_not_equal p v1 v2 then has_changed := true;
	end;
	));
      if !has_changed then PS.singleton Difference else PS.empty
    end

    let separation reach notreach p = begin
      let has_changed = ref false in
      P.iter_vertex p (fun v -> 
	match P.pred p v reach with 
	| [] | [_] -> ()
	| preds ->
	    List.iter (fun a -> List.iter (fun b -> if not(Vertex.equal a b) then begin
	      if P.are_explicitly_not_equal p a b && P.mem_edge p v a notreach && P.mem_edge p v b notreach then begin
		if not(P.mem_edge p a b reach) && P.add_edge p a b notreach then has_changed := true;
		if not(P.mem_edge p b a reach) && P.add_edge p b a notreach then has_changed := true;
	      end;
	    end;) preds) preds;
	    );
      if !has_changed then PS.from notreach else PS.empty
    end
    let separation' reach notreach p = begin
      P.iter_vertex p (fun x -> P.iter_vertex p (fun y -> 
	if not(Vertex.equal x y) &&
	  not(P.mem_edge p x y reach) && not(P.mem_edge p x y notreach)
(* 	    && not(P.mem_edge p y x reach) && not(P.mem_edge p y x notreach) *)
	then begin
	  let res = ref [] in
	  begin try
	    let p' = P.clone p in
	    if debugSaturationDeep then Debug.print "First branching case: Adding %s\n" (Edge.string_of x y reach);
	    ignore( P.add_edge p x y reach );
	    res := (p',PS.from reach) :: !res;
	  with Inconsistent -> (); end;
	  begin try
	    if debugSaturationDeep then Debug.print "Second branching case: Adding %s\n" (Edge.string_of x y notreach);
	    ignore( P.add_edge p x y notreach );
	    res := (p, PS.from notreach) :: !res;
	  with Inconsistent -> (); end;
	  match !res with
	  | [] -> if debugSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugSaturationDeep then print_branching_with !res; raise (Branching !res);
	end;
	););
    end

(* one successor is a function, if x->y and x-*->z then either x=z or y-*->z *)
    let function_successor_reachability reach immreach p = begin
      let inspect (x:vertex) (y:vertex) (z:vertex) = begin
	if not(Vertex.equal x z) && not(P.mem_edge p y z reach) then begin
	  if debugSaturationDeep then Debug.print "%s and %s are 2 separate vertices and %s not present\n" (Vertex.string_of x) (Vertex.string_of z) (Edge.string_of y z reach);
	  let res = ref [] in
	  begin try
	    let p' = P.clone p in
	    if debugSaturationDeep then Debug.print "First branching case: Merging %s and %s\n" (Vertex.string_of x) (Vertex.string_of z);
	    P.merge_vertices p' x z;
	    res := (p',PS.singleton Equality) :: !res;
	  with Inconsistent -> (); end;
	  begin try
	    if debugSaturationDeep then
	      Debug.print "Second branching case: adding %s AND make not equal %s and %s\n" (Edge.string_of y z reach) (Vertex.string_of x) (Vertex.string_of z);
	    ignore( P.add_edge p y z reach );
	    ignore( P.make_not_equal p x z );
	    res := (p, PS.add Difference (PS.from reach)) :: !res;
	  with Inconsistent -> (); end;
	  match !res with
	  | [] -> if debugSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugSaturationDeep then print_branching_with !res; raise (Branching !res);
	end;
      end in 
      P.iter_edge p immreach (fun x y -> List.iter (inspect x y) (P.succ p x reach););
    end

(* in a one successors cycle, a reachable elements needs to be one of the cycle members *)
    let identify_cycle reach immreach p = begin

  (* special case: a black-hole *)
      P.iter_edge p immreach (fun src dst ->
	if Vertex.equal src dst then begin
	  if debugSaturationDeep then Debug.print "I found a cycle of size one: %s\n" (Vertex.string_of src);
	  let has_changed = ref false in
	  P.iter_succ p src reach (fun t ->
	    if not(Vertex.equal src t) then begin
	      if debugSaturation then P.log_message p "cycle of size one";
	      if debugSaturationDeep then Debug.print "Cycle of size one: merging %s and %s\n" (Vertex.string_of src) (Vertex.string_of t);
	      P.merge_vertices p t src; (* t disappears. might raise an inconsistency *)
	      has_changed := true;
	    end;);
	  if !has_changed then raise (Branching [(p,PS.singleton Equality)]);
	end;);

  (* otherwise *)
      P.iter_edge p reach (fun x t ->
	if (Vertex.equal x t) then begin 
	  match P.get_cycle p x immreach with
	  | [] -> ()
	  | cycle_vertices when List.fold_left (fun acc v -> acc && not(Vertex.equal t v)) true cycle_vertices -> begin
	(* if t is not in the cycle yet, identify it with one of the cycle vertices *)
	      let res = ref [] in
	      ignore( List.fold_left (fun original v ->
   	  (* clone first and add the anti-info to the original *)
		let p' = P.clone original in
		ignore( P.make_not_equal original v t ); (* should return true all the time *)
		begin try
		  if debugSaturation then P.log_message p' "cycle";
		  P.merge_vertices p' v t;
		  res := (p',PS.add Difference (PS.singleton Equality)) :: !res;
		with Inconsistent -> () end;
		original) p cycle_vertices );
	      match !res with
	      | [] -> if debugSaturationDeep then Debug.print "All branches are inconsistent\n"; raise Inconsistent;
	      | _ -> if debugSaturationDeep then print_branching_with !res; raise (Branching !res);
	  end
	  | _ -> ()
	end;);
    end

(* 7: an scc reaches an element outside the scc if the later is a singleton *)
    let scc reach p = begin
      let inspect x y z = begin
	if not(Vertex.equal x z) && not(Vertex.equal x y) && not(P.mem_edge p z x reach) then begin
	  let res = ref [] in
	  begin try
	    let p' = P.clone p in 
	    if debugSaturationDeep then Debug.print "First branching case: merging %s and %s AND adding %s (anti-edge)\n"
		(Vertex.string_of x) (Vertex.string_of y) (Edge.string_of z x (Edge.anti reach));
	    ignore( P.add_edge p' z x (Edge.anti reach) ); 
	    P.merge_vertices p' x y;
	    res := (p', PS.add Difference (PS.from (Edge.anti reach))) :: !res;
	  with Inconsistent -> (); end;
	  begin try
	    if debugSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of z x reach);
	    ignore( P.add_edge p z x reach);
	    res := (p, PS.from reach) :: !res;
	  with Inconsistent -> (); end;
	  match !res with
	  | [] -> if debugSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugSaturationDeep then print_branching_with !res; raise (Branching !res);
	end;
      end in
      P.iter_edge p reach (fun x y -> if P.mem_edge p y x reach then P.iter_succ p x reach (inspect x y););
    end

(* there is a total order among the reachable nodes *)
    let total_reachability reach p = begin
      let inspect y z = begin
	if not(Vertex.equal y z) && not( P.mem_edge p z y reach ) && not( P.mem_edge p y z reach ) then begin
	  let res = ref [] in
	  begin try
	    let p' = P.clone p in 
	    if debugSaturationDeep then Debug.print "First branching case: adding %s AND adding %s (anti-edge)\n" (Edge.string_of y z reach) (Edge.string_of z y (Edge.anti reach));
	    ignore( P.add_edge p' y z reach );
	    ignore( P.add_edge p' z y (Edge.anti reach) );
	    res := (p', PS.add_from reach (PS.from (Edge.anti reach))) :: !res;
	  with Inconsistent -> (); end;
	  begin try
	    if debugSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of z y reach);
	    ignore( P.add_edge p z y reach ); 
	    res := (p, PS.from reach) :: !res;
	  with Inconsistent -> (); end;
	  match !res with
	  | [] -> if debugSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugSaturationDeep then print_branching_with !res; raise (Branching !res);
	end
      end in
      P.iter_edge p reach (fun x y -> P.iter_succ p x reach (inspect y));
    end

    let differenciate_dirty_data p : unit = begin
      P.iter_vertex p (fun v1 -> P.iter_vertex p (fun v2 -> if Vertex.is_dirty_and_colored v1 && Vertex.is_dirty_and_colored v2 then begin
	if not(Vertex.equal v1 v2) && not(P.are_explicitly_not_equal p v1 v2) then begin 
	  let res = ref [] in
	  begin try
	    let p' = P.clone p in 
	    if debugSaturationDeep then Debug.print "First branching case: Merging %s and %s\n" (Vertex.string_of v1) (Vertex.string_of v2);
	    P.merge_vertices p' v1 v2;
	    res := (p', PS.singleton Equality) :: !res;
	  with Inconsistent -> (); end;
	  begin try
	    if debugSaturationDeep then
	      Debug.print "Second branching case: making %s and %s explicitely different\n" (Vertex.string_of v1) (Vertex.string_of v2);
	    if debugSaturation then P.log_message p "differenciation with dirty colored";
	    ignore( P.make_not_equal p v1 v2 );
	    res := (p, PS.singleton Difference) :: !res;
	  with Inconsistent -> (); end;
	  match !res with
	  | [] -> if debugSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugSaturationDeep then print_branching_with !res; raise (Branching !res);
	end;
      end;););
    end

    let resolve_difference p : unit = begin
      P.iter_vertex p (fun v1 -> P.iter_vertex p (fun v2 ->
	if not(Vertex.equal v1 v2) && not(P.are_explicitly_not_equal p v1 v2) then begin 
	  let res = ref [] in
	  begin try
	    let p' = P.clone p in 
	    if debugSaturationDeep then Debug.print "First branching case: Merging %s and %s\n" (Vertex.string_of v1) (Vertex.string_of v2);
	    P.merge_vertices p' v1 v2;
	    res := (p', PS.singleton Equality) :: !res;
	  with Inconsistent -> (); end;
	  begin try
	    if debugSaturationDeep then
	      Debug.print "Second branching case: making %s and %s explicitely different\n" (Vertex.string_of v1) (Vertex.string_of v2);
	    ignore( P.make_not_equal p v1 v2 );
	    res := (p, PS.singleton Difference) :: !res;
	  with Inconsistent -> (); end;
	  match !res with
	  | [] -> if debugSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugSaturationDeep then print_branching_with !res; raise (Branching !res);
	end;););
    end

    let resolve_reachability reach notreach p : unit = begin
      P.iter_vertex p (fun v1 -> P.iter_vertex p (fun v2 ->
	if not(P.mem_edge p v1 v2 reach) && not(P.mem_edge p v1 v2 notreach) then begin 
	  let res = ref [] in
	  begin try
	    let p' = P.clone p in 
	    if debugSaturationDeep then Debug.print "First branching case: Adding %s\n" (Edge.string_of v1 v2 reach);
	    ignore( P.add_edge p' v1 v2 reach);
	    res := (p', PS.from reach) :: !res;
	  with Inconsistent -> (); end;
	  begin try
	    if debugSaturationDeep then
	      Debug.print "Second branching case: Adding %s\n" (Edge.string_of v1 v2 notreach);
	    ignore( P.add_edge p v1 v2 notreach);
	    res := (p, PS.from notreach) :: !res;
	  with Inconsistent -> (); end;
	  match !res with
	  | [] -> if debugSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugSaturationDeep then print_branching_with !res; raise (Branching !res);
	end;););
    end

    let resolve_allocation immreach p : unit = begin
      P.iter_vertex p (fun v -> if Vertex.is_eventually_deallocated v then begin
	let res = ref [] in
	begin try
	  let p' = P.clone p in
	  let v_ = P.vbottom p' in
	  if debugSaturationDeep then Debug.print "First branching case: making %s deallocated AND adding %s\n" (Vertex.string_of v) (Edge.string_of v v_ immreach);
	  let changes = ref (PS.singleton Allocation) in
	  Vertex.make_deallocated (P.find_vertex p' v);
	  if P.add_edge p' v v_ immreach then changes := PS.add_from immreach !changes;
	  res := (p', !changes ) :: !res;
	with Inconsistent -> (); end;
	begin try
	  if debugSaturationDeep then Debug.print "Second branching case: making %s allocated\n" (Vertex.string_of v);
	  Vertex.make_allocated v;
	  res := (p, PS.singleton Allocation) :: !res;
	with Inconsistent -> (); end;
	match !res with
	| [] -> if debugSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	| _ -> if debugSaturationDeep then print_branching_with !res; raise (Branching !res);
      end;);
    end

    let allocation reach p = begin
      let has_changed = ref false in
      let v_ = P.vbottom p in
      P.iter_vertex p (fun v ->
	if Vertex.is_eventually_deallocated v then begin
	  try P.iter_succ p v reach (fun v' -> if P.are_explicitly_not_equal p v v_ then begin Vertex.make_allocated v; raise Stop; end;);
	  with Stop -> has_changed := true;
	end;);
      if !has_changed then PS.singleton Allocation else PS.empty
    end

    let deallocation_to_bottom immreach p = begin
      let has_changed, v_ = ref false, P.vbottom p in
      P.iter_vertex p (fun v ->	if Vertex.is_deallocated v && P.add_edge p v v_ immreach then has_changed := true;);
      if !has_changed then PS.from immreach else PS.empty
    end

    let non_interfering_cycles reach notreach p = begin
      let has_changed = ref false in
      P.iter_edge p reach (fun x y  ->
	if P.are_explicitly_not_equal p x y then begin
	  P.iter_succ p y reach (fun z ->
	    if P.mem_edge p z x notreach then begin
	      if P.add_edge p y x notreach then has_changed := true;
	    end;);
	end;);
      if !has_changed then PS.from notreach else PS.empty
    end

    let non_reaching_cycles reach notreach p = begin
      let has_changed = ref false in
      P.iter_edge p reach (fun x y  ->
	if P.are_explicitly_not_equal p x y && P.mem_edge p y x reach then begin
	  P.iter_pred p y notreach (fun t ->
	    assert( not(Vertex.equal t x) && not(Vertex.equal t y) );
	    P.iter_pred p t reach (fun z -> if P.add_edge p z y notreach then has_changed := true;); );
	end;);
      if !has_changed then PS.from notreach else PS.empty
    end

    let reaching_order reach immreach notreach p = begin
      let has_changed = ref false in
      P.iter_edge p immreach (fun x y ->
	P.iter_pred p y reach (fun z ->
	  if not(Vertex.equal z y) then begin
	    if not(Vertex.equal z x) (* && P.are_explicitly_not_equal p x z *) && P.add_edge p x z notreach
	  then has_changed := true;
	end;);
	);
      if !has_changed then PS.from notreach else PS.empty
    end

	(* covered by the previous rule *)
(*     let one_step_joinpoint immreach notreach p = begin *)
(*       let has_changed = ref false in *)
(*       P.iter_edge p immreach (fun x y -> *)
(* 	P.iter_pred p y immreach (fun z -> *)
(* 	  if not(Vertex.equal z x) && P.are_explicitly_not_equal p x z && (P.add_edge p x z notreach || P.add_edge p z x notreach) then has_changed := true; *)
(* 	  );); *)
(*       if !has_changed then PS.from notreach else PS.empty *)
(*     end *)


    let handle_nil_and_bottom reach p = begin
      (* If nil or bottom reaches something, it is equal to that something *)
      let has_changed = ref false in
      let black_hole who = begin
	P.iter_succ p who reach (fun v -> if not(Vertex.equal v who) then begin
	  if debugSaturationDeep then Debug.print "Handling %s in %d: swallowing %s\n" (Vertex.string_of who) (P.id p) (Vertex.string_of v);
	  P.merge_vertices p v who; has_changed := true;
	end;);
      end in
      black_hole (P.vnil p);
      black_hole (P.vbottom p);
      (* one extra check: if they have a common predecessor by reachability, the predicate is inconsistent *)
      let bottom_preds = P.pred p (P.vbottom p) reach in
      P.iter_pred p (P.vnil p) reach (fun v -> List.iter (fun v' -> if Vertex.equal v v' then raise Inconsistent;) bottom_preds);
      (* if P.is_inconsistent ~force:true p then raise Inconsistent; *)
      if !has_changed then PS.singleton Equality else PS.empty
    end

    let _saturate porg ~non_branching_rules ~branching_rules : p list = begin

      let w,finals = Queue.create (), Queue.create () in
      let step = ref 0 in
      if not(P.is_inconsistent ~force:true porg) then
	Queue.add (porg, (non_branching_rules,[]),(branching_rules,[])) w;

      let rec apply_nb p (nb,br) =
	match fst nb with
	| [] -> nb,br (* no more active linear rule *)
	| ((name,f,_) as r)::others ->
	    if debugSaturation then Debug.print "• %s on %d (step %d)\n" name (P.id p) !step;
	    Debug.level (1);
	    let changes = f p in
	    Debug.level (-1);
	    if debugSaturation && not(PS.is_empty changes) then begin
	      P.log_message p name;
	      Debug.level (1);
	      Debug.print "=> has changed something (in step %d)\n" !step;
	      Debug.level (1);
	      Debug.print "%s\n" (PS.string_of changes);
	      Debug.level (-2);
	    end;
	    if saturationSleeping then begin Debug.level 1; Debug.print "%s goes to sleep\n" name; Debug.level (-1); end;
	    let nb',br' = PS.fold wake_up changes ((others, r::(snd nb)),br) in
	    apply_nb p (nb',br')
      and apply_br p (nb,br) =
	match fst br with
	| [] -> assert( List.length (fst nb) = 0);
	    if debugSaturationDeep then Debug.print "--- Could not be augmented => adding %d to finals\n" (P.id p);
	    assert( not(P.is_inconsistent ~force:true p) );
	    if debugSaturation then begin
	      P.log_message p (sprintf "---- saturated (id: %d)----" (P.id p));
	      P.to_dot p (sprintf "tmp/_debug/saturation-final-%d-(%d)" (P.id p) (P.id porg));
	    end;
	    P.clean p;
	    Queue.add p finals;
	| ((name,f,_) as r)::others ->
	    if debugSaturation then Debug.print "• %s on %d (step %d)\n" name (P.id p) !step;
	    Debug.level (1);
	    try f p;
	      Debug.level (-1);
	      if debugSaturation then Debug.print "\t=> not applicable\n";
	      if saturationSleeping then begin Debug.level 1; Debug.print "%s goes to sleep\n" name; Debug.level (-1); end;
	      apply_br p (nb, (others,r::(snd br))) (* not applicable => goes to sleep *)
	    with Branching pList -> assert(List.length pList > 0);
	      Debug.level (-1);
	      List.iter (fun (p',changes) -> begin
		assert( not(PS.is_empty changes) );
		if debugSaturation then begin
		  P.log_message p' name;
		  Debug.level (1); Debug.print "=> has changed something (in step %d)\n" !step;
		  Debug.level (1); Debug.print "%s\n" (PS.string_of changes);
		  Debug.level (-2);
		  Debug.print "For %d, " (P.id p');
		end;
		let nb',br' = PS.fold wake_up changes (nb,br) in (* doesn't go to sleep *)
		Queue.add (p',nb',br') w;
		if debugSaturationDeep then Debug.print "adding %d back to the queue\n" (P.id p');
	      end) pList;
	      
      and wake_up (rinfo:predicate) ((active_nb,sleeping_nb),(active_br,sleeping_br)) = begin
	let (active_nb',sleeping_nb'),(active_br',sleeping_br') =
	  let split (name,_,premices) = List.mem rinfo premices in
	  List.partition split sleeping_nb, List.partition split sleeping_br
	in
	if saturationSleeping then begin
	  if ((List.length active_nb') + (List.length active_br')) > 0 then Debug.print "Waking up:\n"; Debug.level (1);
	  List.iter (fun (name,_,_) -> Debug.print "- %s\n" name) active_nb'; List.iter (fun (name,_,_) -> Debug.print "%s\n" name) active_br';
	  Debug.level (-1);
	end;
	(active_nb @ active_nb', sleeping_nb') , (active_br @ active_br', sleeping_br')
      end
      and work () : unit =
	let (p,nb,br) = Queue.take w in
	incr step;
	if debugSaturation then begin
	  Debug.print "STEP %d: I pick %d from the saturation queue\n" !step (P.id p);
	  P.to_dot p (sprintf "tmp/_debug/step-%d-satqueue-%d" !step (P.id p));
	end;
	try
	  if debugSaturation then Debug.print "starting non-branching rules (phase 1) on %d\n" (P.id p);
	  if debugSaturationDeep then print_rules nb br;
	  let nb',br' = apply_nb p (nb,br) in
	  if debugSaturation then Debug.print "starting branching rules (phase 2) on %d\n" (P.id p);
	  if debugSaturationDeep then print_rules nb' br';
	  apply_br p (nb',br');
	  if debugSaturation then Debug.print "Loop: work again\n";
	  work ();
	with Inconsistent ->
	  Debug.level (-1);
	  if debugSaturation then begin
	    Debug.print "\t=> %d was made inconsistent\n" (P.id p);
	    P.to_dot p (sprintf "tmp/_debug/inconsistent-%d" (P.id p));
	  end;
	  
	  work ();
      and print_rules (active_nb,sleeping_nb) (active_br,sleeping_br) =
	()
(*     Debug.level (1); *)
(* (\*     Debug.print "Active non branching rules\n"; *\) *)
(* (\*     Debug.level (1); List.iter (fun (name,_,_) -> Debug.print "%s\n" name) active_nb; Debug.level (-1); *\) *)
(*     Debug.print "Sleeping non branching rules (%d/%d)\n" (List.length sleeping_nb) nb_nb; *)
(*     if saturationSleeping then begin Debug.level (1); List.iter (fun (name,_,_) -> Debug.print "%s\n" name) sleeping_nb; Debug.level (-1); end; *)
(* (\*     Debug.print "Active branching rules\n"; *\) *)
(* (\*     Debug.level (1); List.iter (fun (name,_,_) -> Debug.print "%s\n" name) active_br; Debug.level (-1); *\) *)
(*     Debug.print "Sleeping branching rules (%d/%d)\n" (List.length sleeping_br) nb_br; *)
(*     if saturationSleeping then begin Debug.level (1); List.iter (fun (name,_,_) -> Debug.print "%s\n" name) sleeping_br; Debug.level (-1); end; *)
(*     Debug.level (-1); *)
      in
      begin try work (); with Queue.Empty -> () end;
      if debugSaturation then Debug.print "=== Finally, saturating %s created %d constraints\n" (P.string_of porg) (Queue.length finals);
      Queue.fold (fun acc el -> el::acc) [] finals
    end

    let apply p : p list = begin
      if debugSaturation then begin
	Debug.print "====\nStarting saturation (all information) on %s\n" (P.string_of p);
	P.log_message p "---- saturation (all information) ----";
      end;
      _saturate p
	~non_branching_rules:(
      [("self reachability",self_reachability Reachable,[]); (* 1.3 *)
	("handle # and _",handle_nil_and_bottom Reachable,[Reachability;Equality;]);
	("induce differenciation",induce_differenciation,[ImmediateReachability;NonImmediateReachability;Reachability;NonReachability;Equality;]); (* 1.1 *)
	("differenciate with locality",differenciate_with_locality, [Locality]); (* 1.2 *)
	("complete_reachability_positive",complete_reachability_positive,[ImmediateReachability;Reachability;Equality;]); (* 1.4 *)
	("complete_reachability_negative",complete_reachability_negative NotReachable NotOneStepReachable,[NonReachability;Equality;]); (* 1.5 *)
	("identify_one_reachable",identify_one_reachable OneStepReachable,[ImmediateReachability;Equality;]); (* 1.6 *)
	("share_reachability",share_reachability OneStepReachable Reachable,[ImmediateReachability;Difference;Reachability;Equality;]);  (* 1.7 *)
	("propagating_non_reachability",propagating_non_reachability NotReachable Reachable,[Reachability;NonReachability;Equality;]); (* 1.8 *)
	("propagating_scc_reachability",propagating_scc_reachability NotReachable Reachable,[NonReachability;Reachability;Equality;]); (* 1.9 *)
	("propagating_non_one_reachability",propagating_non_one_reachability NotOneStepReachable OneStepReachable,[Difference;ImmediateReachability;Equality;]); (* 1.10 *)
	("stepping",stepping Reachable NotOneStepReachable,[Reachability;(* Difference; *)Equality;]); (* 1.2?? *)
	("propagate_globality",propagate_globality Reachable,[Locality;Equality;Reachability;]); (* 1.11*)
	("non_reachability_with_globality",non_reachability_with_globality NotReachable,[Locality;]); (* 1.13 *)
	("propagate_locality",propagate_locality Reachable,[Locality;Reachability;Equality;]); (* 1.12, 1.14 *)
	("resolve_data_difference",resolve_data_difference,[Equality;]);
	("separation",separation Reachable NotReachable,[Difference;Reachability;NonReachability;]);
	("non_interfering_cycles",non_interfering_cycles Reachable NotReachable,[Reachability;Difference;NonReachability;Equality;]); (* 1.22 *)
	("non_reaching_cycles",non_reaching_cycles Reachable NotReachable,[Reachability;Difference;NonReachability;Equality;]); (* 1.2?? *)
(* 	("reaching_order",reaching_order Reachable OneStepReachable NotReachable,[Reachability;ImmediateReachability;(\* Difference; *\)Equality;]); (\* 1.2?? *\) *)
	("check allocation",allocation Reachable,[Equality;Allocation;Reachability;]);
	("make deallocation to bottom",deallocation_to_bottom OneStepReachable,[ImmediateReachability;]);
      ])
	~branching_rules:(
      [("resolve_difference",resolve_difference,[]); (* 1.21 - keep it here. Important for next-saturation *)
(* 	("resolve_reachability",resolve_reachability Reachable NotReachable,[Reachability;NonReachability;]); *)
	("function_successor_reachability",function_successor_reachability Reachable OneStepReachable,[ImmediateReachability;Reachability;Equality;]);  (* 1.16 *)
	("identify_cycle",identify_cycle Reachable OneStepReachable,[ImmediateReachability;Reachability;Equality;]);  (* 1.17 *)
	("scc",scc Reachable,[Reachability;Equality;]);  (* 1.18 *)
	("total_reachability",total_reachability Reachable,[Reachability;Equality;]);  (* 1.19 *)
	("differenciate_dirty_data",differenciate_dirty_data,[Equality;Locality;]); (* 1.20 *)
(* 	("separation (if unknown reachability)",separation' Reachable NotReachable,[Reachability;NonReachability;]); *)
      ])
    end

    let clean_colors p = begin
      P.iter_edges p (fun src dst e -> match e with | Reachable | NotReachable | OneStepReachable | NotOneStepReachable -> P.remove_edge p src dst e; | _ -> ());
      P.iter_edges p (fun src dst e -> match e with
      | ReachableInTheNew ->
	  P.remove_edge p src dst e;
	  ignore( P.add_edge p src dst Reachable );
      | NotReachableInTheNew ->
	  P.remove_edge p src dst e;
	  ignore( P.add_edge p src dst NotReachable );
      | OneStepReachableInTheNew ->
	  P.remove_edge p src dst e;
	  ignore( P.add_edge p src dst OneStepReachable );
      | NotOneStepReachableInTheNew ->
	  P.remove_edge p src dst e;
	  ignore( P.add_edge p src dst NotOneStepReachable );
      | _ -> ());
      if debugNextSaturation then P.log_message p "---- next-saturated ----"; 
      p
    end

    let is_not_colored p = begin
      try P.iter_edges p (fun _ _ e -> match e with
      | ReachableInTheNew | NotReachableInTheNew | OneStepReachableInTheNew | NotOneStepReachableInTheNew -> raise Inconsistent;
      | _ -> ()); true
      with Inconsistent -> false
    end

    let print_v v_ = match v_ with | None -> "none" | Some v -> Vertex.string_of v

(*   let double_merge p (a,b) (c,d) : unit = begin *)
(*   (\* double_merge is always used on a clone, so (a,b)(c,d) must be refetched. Safe anyway to refetch! *\) *)
(*     assert( not(Vertex.equal a b && Vertex.equal c d) ); *)
(*     if debugSaturationDeep then Debug.print "double merging %s and %s + %s and %s\n" *)
(* 	(Vertex.string_of a) (Vertex.string_of b) (Vertex.string_of c) (Vertex.string_of d); *)
(*     match Vertex.equal a b with *)
(*     | true -> assert( not(Vertex.equal c d) ); *)
(* 	merge_vertices p c d; *)
(*     | _ -> *)
(* 	let kept,killed = merge_vertices_ p a b in *)
(* 	match Vertex.equal c killed, Vertex.equal d killed with *)
(* 	|	true,true -> () *)
(* 	|	true,false -> if not(Vertex.equal kept d) then merge_vertices p kept d; *)
(* 	|	false,true -> if not(Vertex.equal c kept) then merge_vertices p c kept; *)
(* 	|	false,false -> if not(Vertex.equal c d) then merge_vertices p c d; *)
(*   end *)

(* (\* Next_saturation 1.1: One successors are updated or copied. *\) *)
(* let update_one_successors x y p = begin *)
(*   let g,vx,vy = p.storage, get_vertex p x, get_vertex p y in *)
(*   let vx_succ = get_succ p vx in *)
(*   if debugNextSaturation then Debug.print "[vx:%s, vy:%s, vold:%s]\n" (Vertex.string_of vx) (Vertex.string_of vy) (print_v vx_succ); *)

(*   P.iter_edge (fun t1 t2 ->  *)
(*     if debugNextSaturationDeep then Debug.print "Inspecting %s in %d\n" (Edge.string_of t1 t2 OneStepReachable) (P.id p); *)

(*     if not(P.mem_edge g t1 t2 OneStepReachableInTheNew) then begin *)
(*       match vx_succ with *)
(*       | None when not(Vertex.equal t1 vx) -> begin *)
(* 	  if debugNextSaturationDeep then Debug.print "* no succ to %s\n" (Vertex.string_of vx); *)
(* 	  let res = ref [] in *)
(* 	  begin try *)
(* 	    let p' = clone p in  *)
(* 	    if debugNextSaturationDeep then Debug.print "First branching case: Merging %s and %s\n" (Vertex.string_of vx) (Vertex.string_of t1); *)
(* 	    if debugNextSaturation then P.log_message p' "next_saturation: one successor"; *)
(* 	    ignore( add_edge p'.storage t1 t2 (Edge.anti OneStepReachableInTheNew) ); *)
(* 	    merge_vertices p' vx t1; *)
(* 	    res := (p', PS.singleton Equality) :: !res; *)
(* 	  with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(* 	  begin try *)
(* 	    if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 OneStepReachableInTheNew); *)
(* 	    if debugNextSaturation then P.log_message p "next_saturation: one successor"; *)
(* 	    ignore( add_edge g t1 t2 OneStepReachableInTheNew ); *)
(* 	    res := (p, PS.from OneStepReachableInTheNew) :: !res; *)
(* 	  with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(* 	  match !res with *)
(* 	  | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent; *)
(* 	  | pList ->  *)
(* 	      if debugNextSaturationDeep then print_branching_with !res; *)
(* 	      raise (Branching pList); *)
(*       end *)
(*       | Some vold when not(Vertex.equal t1 vx && Vertex.equal t2 vold) -> begin *)
(* 	  if debugNextSaturationDeep then Debug.print "* succ of %s: %s\n" (Vertex.string_of vx) (Vertex.string_of vold); *)
(* 	  let res = ref [] in *)
(* 	  begin try *)
(* 	    if debugNextSaturationDeep then *)
(* 	      Debug.print "First branching case: Merging %s and %s AND %s and %s\n" *)
(* 		(Vertex.string_of vx) (Vertex.string_of t1) (Vertex.string_of vold) (Vertex.string_of t2); *)
(* 	    let p' = clone p in  *)
(* 	    if debugNextSaturation then P.log_message p' "next_saturation: one successor"; *)
(* 	    let changes = ref (PS.singleton Equality) in *)
(* 	    if add_edge p'.storage t1 t2 (Edge.anti OneStepReachableInTheNew) then *)
(* 	      changes := PS.add_from (Edge.anti OneStepReachableInTheNew) !changes; *)
(* 	    double_merge p' (vx,t1) (vold,t2); *)
(* 	    res := (p', !changes) :: !res; *)
(* 	  with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(* 	  begin try *)
(* 	    if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 OneStepReachableInTheNew); *)
(* 	    if debugNextSaturation then P.log_message p "next_saturation: one successor"; *)
(* 	    let changes = ref PS.empty in *)
(* 	    if add_edge g t1 t2 OneStepReachableInTheNew then *)
(* 	      changes := PS.add_from OneStepReachableInTheNew !changes; *)
(* 	    res := (p, !changes) :: !res; *)
(* 	  with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(* 	  match !res with *)
(* 	  | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent; *)
(* 	  | pList ->  *)
(* 	      if debugNextSaturationDeep then print_branching_with !res; *)
(* 	      raise (Branching pList); *)
(*       end *)
(*       | _ -> () (\* doesn't apply *\) *)
(*     end; *)
(*   ) OneStepReachable g; *)
(* end *)

(* (\* Next_saturation 1.2 *\) *)
(* let update_one_successors_reverse x y p = begin *)
(*   let g,vx,vy = p.storage, get_vertex p x, get_vertex p y in *)
(*   if debugNextSaturation then Debug.print "[vx:%s, vy:%s]\n" (Vertex.string_of vx) (Vertex.string_of vy); *)

(*   P.iter_edge (fun t1 t2  -> *)
(*     if debugNextSaturationDeep then Debug.print "Inspecting %s in %d\n" (Edge.string_of t1 t2 OneStepReachableInTheNew) (P.id p); *)
      
(*     if not(P.mem_edge g t1 t2 OneStepReachable) && not(Vertex.equal t1 vx && Vertex.equal t2 vy) then begin  *)
(*       let res = ref [] in *)
(*       begin try *)
(* 	if debugNextSaturationDeep then *)
(* 	  Debug.print "First branching case: Merging %s and %s AND %s and %s AND adding %s (anti-edge)\n" *)
(* 	    (Vertex.string_of vx) (Vertex.string_of t1) (Vertex.string_of vy) (Vertex.string_of t2) (Edge.string_of t1 t2 (Edge.anti OneStepReachable)); *)
(* 	let p' = clone p in  *)
(* 	if debugNextSaturation then P.log_message p' "next_saturation: one successor reverse"; *)
(* 	let changes = ref (PS.singleton Equality) in *)
(* 	if add_edge p'.storage t1 t2 (Edge.anti OneStepReachable) then *)
(* 	  changes := PS.add_from (Edge.anti OneStepReachable) !changes; *)
(* 	double_merge p' (vx,t1) (vy,t2); *)
(* 	res := (p', !changes) :: !res; *)
(*       with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(*       begin try *)
(* 	if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 OneStepReachable); *)
(* 	if debugNextSaturation then P.log_message p "next_saturation: one successor reverse"; *)
(* 	let changes = ref PS.empty in *)
(* 	if add_edge g t1 t2 OneStepReachable then *)
(* 	  changes := PS.add_from OneStepReachable !changes; *)
(* 	res := (p, !changes) :: !res; *)
(*       with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(*       match !res with *)
(*       | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent; *)
(*       | pList ->  *)
(* 	  if debugNextSaturationDeep then print_branching_with !res; *)
(* 	  raise (Branching pList); *)
(*     end; *)
(*     ) OneStepReachableInTheNew g; *)
(* end *)

(* (\* Next_saturation 2.1: Not One-successors are updated or copied. *\) *)
(* let update_not_one_successors x y p = begin *)
(*   let g,vx,vy = p.storage, get_vertex p x, get_vertex p y in *)
(*   if debugNextSaturation then Debug.print "[vx:%s, vy:%s]\n" (Vertex.string_of vx) (Vertex.string_of vy); *)

(*   P.iter_edge (fun t1 t2 ->  *)
(*     if debugNextSaturationDeep then Debug.print "Inspecting %s in %d\n" (Edge.string_of t1 t2 NotOneStepReachable) (P.id p); *)

(*     if not(P.mem_edge g t1 t2 NotOneStepReachableInTheNew) && not(Vertex.equal t1 vx && Vertex.equal t2 vy) then begin  *)
(*       let res = ref [] in *)
(*       begin try *)
(* 	if debugNextSaturationDeep then *)
(* 	  Debug.print "First branching case: Merging %s and %s AND %s and %s AND adding %s (anti-edge)\n" *)
(* 	    (Vertex.string_of vx) (Vertex.string_of t1) (Vertex.string_of vy) (Vertex.string_of t2) (Edge.string_of t1 t2 (Edge.anti NotOneStepReachableInTheNew)); *)
(* 	let p' = clone p in  *)
(* 	if debugNextSaturation then P.log_message p' "next_saturation: not one successor"; *)
(* 	let changes = ref (PS.singleton Equality) in *)
(* 	if add_edge p'.storage t1 t2 (Edge.anti NotOneStepReachableInTheNew) then *)
(* 	  changes := PS.add_from (Edge.anti NotOneStepReachableInTheNew) !changes; *)
(* 	double_merge p' (vx,t1) (vy,t2); *)
(* 	res := (p', !changes) :: !res; *)
(*       with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(*       begin try *)
(* 	if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 NotOneStepReachableInTheNew);  *)
(* 	if debugNextSaturation then P.log_message p "next_saturation: not one successor"; *)
(* 	let changes = ref PS.empty in *)
(* 	if add_edge g t1 t2 NotOneStepReachableInTheNew then *)
(* 	  changes := PS.add_from NotOneStepReachableInTheNew !changes; *)
(* 	res := (p, !changes) :: !res; *)
(*       with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(*       match !res with *)
(*       | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent; *)
(*       | pList ->  *)
(* 	  if debugNextSaturationDeep then print_branching_with !res; *)
(* 	  raise (Branching pList); *)
(*     end; *)
(*     ) NotOneStepReachable g; *)
(* end *)

(* (\* Next_saturation 2.2 *\) *)
(* let update_not_one_successors_reverse x y p = begin *)
(*   let g,vx,vy = p.storage, get_vertex p x, get_vertex p y in *)
(*   let vx_succ = get_succ p vx in *)
(*   if debugNextSaturation then Debug.print "[vx:%s, vy:%s, vold:%s]\n" (Vertex.string_of vx) (Vertex.string_of vy) (print_v vx_succ); *)

(*   P.iter_edge (fun t1 t2 -> *)
(*       if debugNextSaturationDeep then Debug.print "Inspecting %s in %d\n" (Edge.string_of t1 t2 NotOneStepReachableInTheNew) (P.id p); *)

(*       if not(P.mem_edge g t1 t2 NotOneStepReachable) then begin *)
(* 	match vx_succ with *)
(* 	| None when not(Vertex.equal t1 vx) -> begin *)
(* 	    if debugNextSaturationDeep then Debug.print "* no succ to %s\n" (Vertex.string_of vx); *)
(* 	    let res = ref [] in *)
(*             begin try *)
(* 	      if debugNextSaturationDeep then Debug.print "First branching case: Merging %s and %s\n" (Vertex.string_of vx) (Vertex.string_of t1); *)
(* 	      let p' = clone p in  *)
(* 	      if debugNextSaturation then P.log_message p' "next_saturation: not one successor reverse"; *)
(* 	      let changes = ref (PS.singleton Equality) in *)
(* 	      if add_edge p'.storage t1 t2 (Edge.anti NotOneStepReachable) then *)
(* 		changes := PS.add_from (Edge.anti NotOneStepReachable) !changes; *)
(* 	      merge_vertices p' vx t1; *)
(* 	      res := (p', !changes) :: !res; *)
(* 	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(* 	    begin try *)
(* 	      if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 NotOneStepReachable); *)
(* 	      if debugNextSaturation then P.log_message p "next_saturation: not one successor reverse"; *)
(* 	      let changes = ref PS.empty in *)
(* 	      if add_edge g t1 t2 NotOneStepReachable then *)
(* 		changes := PS.add_from NotOneStepReachable !changes; *)
(* 	      res := (p, !changes) :: !res; *)
(* 	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(* 	    match !res with *)
(* 	    | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent; *)
(* 	    | pList ->  *)
(* 		if debugNextSaturationDeep then print_branching_with !res; *)
(* 		raise (Branching pList); *)
(* 	end *)
(* 	| Some vold when not(Vertex.equal t1 vx && Vertex.equal t2 vold) -> begin *)
(* 	    if debugNextSaturationDeep then Debug.print "* succ of %s: %s\n" (Vertex.string_of vx) (Vertex.string_of vold); *)
(* 	    let res = ref [] in *)
(* 	    begin try *)
(* 	      if debugNextSaturationDeep then *)
(* 		Debug.print "First branching case: Merging %s and %s AND %s and %s\n" *)
(* 		  (Vertex.string_of vx) (Vertex.string_of t1) (Vertex.string_of vold) (Vertex.string_of t2); *)
(* 	      let p' = clone p in  *)
(* 	      if debugNextSaturation then P.log_message p' "next_saturation: not one successor reverse"; *)
(* 	      let changes = ref (PS.singleton Equality) in *)
(* 	      if add_edge p'.storage t1 t2 (Edge.anti NotOneStepReachable) then *)
(* 		changes := PS.add_from (Edge.anti NotOneStepReachable) !changes; *)
(* 	      double_merge p' (vx,t1) (vold,t2); *)
(* 	      res := (p', !changes) :: !res; *)
(* 	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(* 	    begin try *)
(* 	      if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 NotOneStepReachable); *)
(* 	      if debugNextSaturation then P.log_message p "next_saturation: not one successor reverse"; *)
(* 	      let changes = ref PS.empty in *)
(* 	      if add_edge g t1 t2 NotOneStepReachable then *)
(* 		changes := PS.add_from NotOneStepReachable !changes; *)
(* 	      res := (p, !changes) :: !res; *)
(* 	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end; *)
(* 	    match !res with *)
(* 	    | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent; *)
(* 	    | pList ->  *)
(* 		if debugNextSaturationDeep then print_branching_with !res; *)
(* 		raise (Branching pList); *)
(* 	end *)
(* 	| _ -> () (\* doesn't apply *\) *)
(*       end; *)
(*       ) NotOneStepReachableInTheNew g; *)
(* end *)

(* Next_saturation 3.1: Reachability updates. *)
let update_reachability x y p = begin
  let vx,vy = P.get_vertex p x, P.get_vertex p y in
  let vx_succ = P.get_succ p vx in
  if debugNextSaturation then Debug.print "[vx:%s, vy:%s, vold:%s]\n" (Vertex.string_of vx) (Vertex.string_of vy) (print_v vx_succ);

  P.iter_edge p Reachable (fun t1 t2 ->
    if debugNextSaturationDeep then Debug.print "Inspecting %s in %d\n" (Edge.string_of t1 t2 Reachable) (P.id p);
 
    if not(P.mem_edge p t1 t2 ReachableInTheNew) then begin
      match vx_succ with
      | None when not(P.mem_edge p t1 vx ReachableInTheNew) -> begin
	  if debugNextSaturationDeep then Debug.print "* no succ to %s\n" (Vertex.string_of vx);
	  let res = ref [] in
	  begin
	    let p' = P.clone p in 
	    if debugNextSaturationDeep then Debug.print "First branching case: adding %s AND %s (anti-edge)\n"
		(Edge.string_of t1 vx ReachableInTheNew) (Edge.string_of t1 t2 (Edge.anti ReachableInTheNew));
	    let changes = ref PS.empty in
	    try 
	      if P.add_edge p' t1 vx ReachableInTheNew then
		changes := PS.add_from ReachableInTheNew !changes;
	      if P.add_edge p' t1 t2 (Edge.anti ReachableInTheNew) then
		changes := PS.add_from (Edge.anti ReachableInTheNew) !changes;
	      res := (p', !changes) :: !res;
	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> %d is inconsistent\n" (P.id p'); end;
	  begin
	    if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 ReachableInTheNew);
	    let changes = ref PS.empty in
	    try 
	      if P.add_edge p t1 t2 ReachableInTheNew then
		changes := PS.add_from ReachableInTheNew !changes;
	      res := (p, !changes) :: !res;
	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> %d is inconsistent\n" (P.id p);
	  end;
	  match !res with
	  | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugNextSaturationDeep then print_branching_with !res; raise (Branching !res);
      end
      | Some vold ->
	  if not(P.mem_edge p t1 vx ReachableInTheNew && P.mem_edge p vold t2 ReachableInTheNew) then begin
	    if debugNextSaturationDeep then Debug.print "* succ of %s: %s\n" (Vertex.string_of vx) (Vertex.string_of vold);
	    let res = ref [] in
	    begin
	      let p' = P.clone p in 
	      if debugNextSaturationDeep then
		Debug.print "First branching case: adding %s AND %s AND %s (anti-edge)\n"
		  (Edge.string_of t1 vx ReachableInTheNew) (Edge.string_of vold t2 ReachableInTheNew) (Edge.string_of t1 t2 (Edge.anti ReachableInTheNew));
	      let changes = ref PS.empty in
	      try
		if P.add_edge p' t1 vx ReachableInTheNew then
		  changes := PS.add_from ReachableInTheNew !changes;
		if P.add_edge p' vold t2 ReachableInTheNew then
		  changes := PS.add_from ReachableInTheNew !changes;
		if P.add_edge p' t1 t2 (Edge.anti ReachableInTheNew) then
		  changes := PS.add_from (Edge.anti ReachableInTheNew) !changes;
		res := (p',!changes) :: !res;
	      with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> %d is inconsistent\n" (P.id p');
	    end;
	    begin
	      if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 ReachableInTheNew);
	      let changes = ref PS.empty in
	      try
		if P.add_edge p t1 t2 ReachableInTheNew then
		  changes := PS.add_from ReachableInTheNew !changes;
		res := (p, !changes) :: !res;
	      with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> %d is inconsistent\n" (P.id p);
	    end;
	    match !res with
	    | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	    | _ -> if debugNextSaturationDeep then print_branching_with !res; raise (Branching !res);
	  end;
      | _ -> () (* doesn't apply *)
    end;
    );
end

(* Next_saturation 3.2 *)
  let update_reachability_reverse x y p = begin
    let vx,vy = P.get_vertex p x, P.get_vertex p y in
    if debugNextSaturation then Debug.print "[vx:%s, vy:%s]\n" (Vertex.string_of vx) (Vertex.string_of vy);

    P.iter_edge p ReachableInTheNew (fun t1 t2 ->
      if debugNextSaturationDeep then Debug.print "Inspecting %s in %d\n" (Edge.string_of t1 t2 ReachableInTheNew) (P.id p);
      
      if not(P.mem_edge p t1 t2 Reachable) && not( P.mem_edge p t1 vx Reachable && P.mem_edge p vy t2 Reachable) then begin 
	let res = ref [] in
	begin try
	  if debugNextSaturationDeep then
	    Debug.print "First branching case: adding %s AND %s AND  %s (anti-edge)\n"
	      (Edge.string_of t1 vx Reachable) (Edge.string_of vy t2 Reachable) (Edge.string_of t1 t2 (Edge.anti Reachable));
	  let p' = P.clone p in 
	  let changes = ref PS.empty in
	  if P.add_edge p' t1 vx Reachable then
	    changes := PS.add_from Reachable !changes;
	  if P.add_edge p' vy t2 Reachable then
	    changes := PS.add_from Reachable !changes;
	  if P.add_edge p' t1 t2 (Edge.anti Reachable) then
	    changes := PS.add_from (Edge.anti Reachable) !changes;
	  res := (p',!changes) :: !res;
	with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	begin try
	  if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 Reachable);
	  ignore( P.add_edge p t1 t2 Reachable );
	  res := (p, PS.from Reachable) :: !res;
	with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	match !res with
	| [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	| _ -> if debugNextSaturationDeep then print_branching_with !res; raise (Branching !res);
      end;
      );
  end

(* Next-saturation 3.3 *)
  let update_reachability2 x p = begin
    let vx = P.get_vertex p x in
    if debugNextSaturation then Debug.print "[vx:%s]\n" (Vertex.string_of vx);
    
    P.iter_pred p vx Reachable (fun t1 ->
      P.iter_succ p t1 ReachableInTheNew (fun t2 ->
	
	if not(P.mem_edge p t1 t2 Reachable) && not(P.mem_edge p vx t2 ReachableInTheNew) then begin 
	  let res = ref [] in
	  begin try
	    if debugNextSaturationDeep then
	      Debug.print "First branching case: adding %s AND  %s (anti-edge)\n"
		(Edge.string_of t1 t2 Reachable) (Edge.string_of vx t2 (Edge.anti ReachableInTheNew));
	    let p' = P.clone p in 
	    let changes = ref PS.empty in
	    if P.add_edge p' t1 t2 Reachable then
	      changes := PS.add_from Reachable !changes;
	    if P.add_edge p' vx t2 (Edge.anti ReachableInTheNew) then
	      changes := PS.add_from (Edge.anti ReachableInTheNew) !changes;
	    res := (p', !changes) :: !res;
	  with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	  begin try
	    if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of vx t2 ReachableInTheNew);
	    let changes = ref PS.empty in
	    if P.add_edge p vx t2 ReachableInTheNew then
	      changes := PS.add_from ReachableInTheNew !changes;
	    res := (p, !changes) :: !res;
	  with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	  match !res with
	  | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugNextSaturationDeep then print_branching_with !res; raise (Branching !res);
	end;
	
	);
      );
  end

(* Next-saturation 3.4 *)
  let update_reachability2_reverse x p = begin
    let vx = P.get_vertex p x in
    if debugNextSaturation then Debug.print "[vx:%s]\n" (Vertex.string_of vx);
    
    P.iter_pred p vx ReachableInTheNew (fun t1 ->
      P.iter_succ p t1 Reachable (fun t2 ->
	
	if not(P.mem_edge p t1 t2 ReachableInTheNew) && not(P.mem_edge p vx t2 Reachable) then begin 
	  let res = ref [] in
	  begin try
	    if debugNextSaturationDeep then
	      Debug.print "First branching case: adding %s AND  %s (anti-edge)\n"
		(Edge.string_of t1 t2 ReachableInTheNew) (Edge.string_of vx t2 (Edge.anti Reachable));
	    let p' = P.clone p in 
	    let changes = ref PS.empty in
	    if P.add_edge p' t1 t2 ReachableInTheNew then
	      changes := PS.add_from ReachableInTheNew !changes;
	    if P.add_edge p' vx t2 (Edge.anti Reachable) then
	      changes := PS.add_from (Edge.anti Reachable) !changes;
	    res := (p', !changes) :: !res;
	  with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	  begin try
	    if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of vx t2 Reachable);
	    let changes = ref PS.empty in
	    if P.add_edge p vx t2 Reachable then
	      changes := PS.add_from Reachable !changes;
	    res := (p, !changes) :: !res;
	  with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	  match !res with
	  | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	  | _ -> if debugNextSaturationDeep then print_branching_with !res; raise (Branching !res);
	end;
	
	);
      );
  end

(* Next_saturation 4.2 *)
  let update_non_reachability x y p = begin
    let vx,vy = P.get_vertex p x, P.get_vertex p y in
    if debugNextSaturation then Debug.print "[vx:%s, vy:%s]\n" (Vertex.string_of vx) (Vertex.string_of vy);

    P.iter_edge p NotReachable (fun t1 t2 ->
      if debugNextSaturationDeep then Debug.print "Inspecting %s in %d\n" (Edge.string_of t1 t2 NotReachable) (P.id p);

      if not(P.mem_edge p t1 t2 NotReachableInTheNew) && not( P.mem_edge p t1 vx Reachable && P.mem_edge p vy t2 Reachable ) then begin 
	let res = ref [] in
	begin try
	  if debugNextSaturationDeep then
	    Debug.print "First branching case: Adding %s AND %s AND adding %s (anti-edge)\n"
	      (Edge.string_of t1 vx Reachable) (Edge.string_of vy t2 Reachable) (Edge.string_of t1 t2 (Edge.anti NotReachableInTheNew));
	  let p' = P.clone p in 
	  let changes = ref PS.empty in
	  if P.add_edge p' t1 vx Reachable then
	    changes := PS.add_from Reachable !changes;
	  if P.add_edge p' vy t2 Reachable then
	    changes := PS.add_from Reachable !changes;
	  if P.add_edge p' t1 t2 (Edge.anti NotReachableInTheNew) then
	    changes := PS.add_from (Edge.anti NotReachableInTheNew) !changes;
	  res := (p', !changes) :: !res;
	with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	begin try
	  if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 NotReachableInTheNew);
	  let changes = ref PS.empty in
	  if P.add_edge p t1 t2 NotReachableInTheNew then
	    changes := PS.add_from NotReachableInTheNew !changes;
	  res := (p, !changes) :: !res;
	with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	match !res with
	| [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	| _ -> if debugNextSaturationDeep then print_branching_with !res; raise (Branching !res);
      end;
      );
  end

(* Next_saturation 4.2 *)
  let update_non_reachability_reverse x y p = begin
    let vx,vy = P.get_vertex p x, P.get_vertex p y in
    let vx_succ = P.get_succ p vx in
    if debugNextSaturation then Debug.print "[vx:%s, vy:%s, vold:%s]\n" (Vertex.string_of vx) (Vertex.string_of vy) (print_v vx_succ);

    P.iter_edge p NotReachableInTheNew (fun t1 t2 ->
      if debugNextSaturationDeep then Debug.print "Inspecting %s in %d\n" (Edge.string_of t1 t2 NotReachableInTheNew) (P.id p);

      if not(P.mem_edge p t1 t2 NotReachable) then begin
	match vx_succ with
	| None when not(P.mem_edge p t1 vx ReachableInTheNew) -> begin
	    if debugNextSaturationDeep then Debug.print "* no succ to %s\n" (Vertex.string_of vx);
	    let res = ref [] in
            begin try
	      if debugNextSaturationDeep then Debug.print "First branching case: Adding %s AND adding %s (anti-edge)\n"
		  (Edge.string_of t1 vx ReachableInTheNew) (Edge.string_of t1 t2 (Edge.anti NotReachable));
	      let p' = P.clone p in 
	      let changes = ref PS.empty in
	      if P.add_edge p' t1 vx ReachableInTheNew then
		changes := PS.add_from ReachableInTheNew !changes;
	      if P.add_edge p' t1 t2 (Edge.anti NotReachable) then
		changes := PS.add_from (Edge.anti NotReachable) !changes;
	      res := (p', !changes) :: !res;
	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	    begin try
	      if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 NotReachable);
	      let changes = ref PS.empty in
	      if P.add_edge p t1 t2 NotReachable then
		changes := PS.add_from NotReachable !changes;
	      res := (p, !changes) :: !res;
	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	    match !res with
	    | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	    | _ -> if debugNextSaturationDeep then print_branching_with !res; raise (Branching !res);
	end
	| Some vold when not( P.mem_edge p t1 vx ReachableInTheNew && P.mem_edge p vold t2 ReachableInTheNew ) -> begin
	    if debugNextSaturationDeep then Debug.print "* succ of %s: %s\n" (Vertex.string_of vx) (Vertex.string_of vold);
	    let res = ref [] in
	    begin try
	      if debugNextSaturationDeep then
		Debug.print "First branching case: Adding %s AND %s AND adding %s (anti-edge)\n"
		  (Edge.string_of t1 vx ReachableInTheNew) (Edge.string_of vold t2 ReachableInTheNew) (Edge.string_of t1 t2 (Edge.anti NotReachableInTheNew));
	      let p' = P.clone p in 
	      if debugNextSaturation then P.log_message p' "next_saturation: non reachability reverse";
	      let changes = ref PS.empty in
	      if P.add_edge p' t1 vx ReachableInTheNew then
		changes := PS.add_from ReachableInTheNew !changes;
	      if P.add_edge p' vold t2 ReachableInTheNew then
		changes := PS.add_from ReachableInTheNew !changes;
	      if P.add_edge p' t1 t2 (Edge.anti NotReachable) then
		changes := PS.add_from (Edge.anti NotReachable) !changes;
	      res := (p', !changes) :: !res;
	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	    begin try
	      if debugNextSaturationDeep then Debug.print "Second branching case: adding %s\n" (Edge.string_of t1 t2 NotReachable);
	      let changes = ref PS.empty in
	      if P.add_edge p t1 t2 NotReachable then
		changes := PS.add_from NotReachable !changes;
	      res := (p, !changes) :: !res;
	    with Inconsistent -> if debugNextSaturationDeep then Debug.print "=> Inconsistent\n"; end;
	    match !res with
	    | [] -> if debugNextSaturationDeep then Debug.print "Both branches are inconsistent\n"; raise Inconsistent;
	    | _ -> if debugNextSaturationDeep then print_branching_with !res; raise (Branching !res);
	end;
	| _ -> () (* doesn't apply *)
      end;
      );
  end

      
  module VS = Set.Make(Vertex)

(* Precondition: vnext (if there is) should not be vy *)
  let apply_next p (x:Label.t) (y:Label.t) : p list = begin

    let vx,vy = P.get_vertex p x, P.get_vertex p y in
(*     let succ_x,succ_y = *)
(*       List.fold_left (fun acc dst -> if Vertex.equal dst vx then acc else VS.add dst acc) VS.empty (P.succ p vx Reachable), *)
(*       List.fold_left (fun acc dst -> if Vertex.equal dst vy then acc else VS.add dst acc) VS.empty (P.succ p vy Reachable) *)
(*     in *)
    let res =
(*       if not(VS.is_empty succ_x) && VS.subset succ_x succ_y then begin *)
(*         (\* reconstructing the bridge from x to its old successors, but inserting y in the middle *\) *)
(* 	P.iter_pred p vx Reachable (fun v ->  *)
(* 	  P.remove_edge p v vy NotReachable; *)
(* 	  ignore( P.add_edge p v vy Reachable ); *)
(* 	  ); *)
(* 	match P.get_succ p vx with *)
(* 	| None -> *)
(* 	    P.remove_edge p vx vy NotOneStepReachable; *)
(* 	    ignore( P.add_edge p vx vy OneStepReachable ); *)
(* 	  [p] (\* saturate p *\) *)
(* 	| Some vnext -> (\* vnext should not be vy: precondition for the method call site *\) *)
(* 	    P.remove_edge p vx vnext OneStepReachable; *)
(* 	    ignore( P.add_edge p vx vnext NotOneStepReachable ); *)
(* 	    P.remove_edge p vx vy NotOneStepReachable; *)
(* 	    ignore( P.add_edge p vx vy OneStepReachable ); *)
(* 	    [p] (\* saturate p *\) *)
(*       end else begin *)
	if debugNextSaturation then Debug.print "==== Starting next-saturation on %s (vx:%s, vy:%s)\n" (P.string_of p) (Vertex.string_of vx) (Vertex.string_of vy);
	P.iter_edge p NotOneStepReachable (fun t1 t2 ->
	  if not(Vertex.equal t1 vx && Vertex.equal t2 vy) then ignore( P.add_edge p t1 t2 NotOneStepReachableInTheNew );
	  );
	begin match P.get_succ p vx with
	| None ->
	    P.iter_edge p OneStepReachable (fun t1 t2 ->
	      ignore( P.add_edge p t1 t2 OneStepReachableInTheNew );
	      ignore( P.add_edge p t1 t2 ReachableInTheNew ); (* helps saturation *)
	      );
	| Some vnext -> (* vnext should not be vy: precondition for the method call site *)
	    P.iter_edge p OneStepReachable (fun t1 t2 ->
	      if not(Vertex.equal t1 vx && Vertex.equal t2 vnext) then begin
		ignore( P.add_edge p t1 t2 OneStepReachableInTheNew );
		ignore( P.add_edge p t1 t2 ReachableInTheNew ); (* helps saturation *)
	      end;);
	end;
	ignore( P.add_edge p vx vy OneStepReachableInTheNew );
	if debugNextSaturation then P.log_message p (sprintf "---- next-saturation ----\\n(vx:%s, vy:%s)\n" (Vertex.string_of vx) (Vertex.string_of vy));
	if debugNextSaturationDeep then P.to_dot p (sprintf "tmp/_debug/make-next-start-%d" (P.id p));
	List.map clean_colors
	  (_saturate p
	     ~non_branching_rules:(
	   [("self reachability",self_reachability Reachable,[]); (* 1.3 *)
	     ("self reachability (with colors)",self_reachability ReachableInTheNew,[]); (* 1.3 *)
	     ("handle # and _",handle_nil_and_bottom Reachable,[Reachability;Equality;]);
	     ("handle # and _ (with colors)",handle_nil_and_bottom ReachableInTheNew,[Reachability';Equality;]);
	     ("induce differenciation",induce_differenciation,[ImmediateReachability;NonImmediateReachability;Reachability;NonReachability;Equality;]); (* 1.1 *)
	     ("differenciate with locality",differenciate_with_locality, [Locality]); (* 1.2 *)
	     ("complete_reachability_positive",complete_reachability_positive,[ImmediateReachability;Reachability;ImmediateReachability';Reachability';Equality;]); (* 1.4 *)
	     ("complete_reachability_negative",complete_reachability_negative NotReachable NotOneStepReachable,[NonReachability;Equality;]); (* 1.5 *)
	     ("complete_reachability_negative (with colors)",complete_reachability_negative NotReachableInTheNew NotOneStepReachableInTheNew,[NonReachability';Equality;]); (* 1.5 *)
	     ("identify_one_reachable",identify_one_reachable OneStepReachable,[ImmediateReachability;Equality;]); (* 1.6 *)
	     ("identify_one_reachable (with colors)",identify_one_reachable OneStepReachableInTheNew,[ImmediateReachability';Equality;]); (* 1.6 *)
	     ("share_reachability",share_reachability OneStepReachable Reachable,[ImmediateReachability;Difference;Reachability;Equality;]);  (* 1.7 *)
	     ("share_reachability (with colors)",share_reachability OneStepReachableInTheNew ReachableInTheNew,[ImmediateReachability';Difference;Reachability';Equality;]);  (* 1.7 *)
	     ("propagating_non_reachability",propagating_non_reachability NotReachable Reachable,[Reachability;NonReachability;Equality;]); (* 1.8 *)
	     ("propagating_non_reachability (with colors)",propagating_non_reachability NotReachableInTheNew ReachableInTheNew,[Reachability';NonReachability';Equality;]); (* 1.8 *)
	     ("propagating_scc_reachability",propagating_scc_reachability NotReachable Reachable,[NonReachability;Reachability;Equality;]); (* 1.9 *)
	     ("propagating_scc_reachability (with colors)",propagating_scc_reachability NotReachableInTheNew ReachableInTheNew,[NonReachability';Reachability';Equality;]); (* 1.9 *)
	     ("propagating_non_one_reachability",propagating_non_one_reachability NotOneStepReachable OneStepReachable,[Difference;ImmediateReachability;Equality;]); (* 1.10 *)
	     ("propagating_non_one_reachability (with colors)",
	      propagating_non_one_reachability NotOneStepReachableInTheNew OneStepReachableInTheNew,
	      [Difference;ImmediateReachability';Equality;]); (* 1.10 *)
	     ("stepping",stepping Reachable NotOneStepReachable,[Reachability;(* Difference; *)Equality;]);
	     ("stepping (with colors)",stepping ReachableInTheNew NotOneStepReachableInTheNew,[Reachability';(* Difference; *)Equality;]);
	     ("propagate_globality",propagate_globality Reachable,[Locality;Equality;Reachability;]); (* 1.11*)
	     ("propagate_globality (with colors)",propagate_globality ReachableInTheNew,[Locality;Equality;Reachability';]); (* 1.11*)
	     ("non_reachability_with_globality",non_reachability_with_globality NotReachable,[Locality;]); (* 1.13 *)
	     ("non_reachability_with_globality (with colors)",non_reachability_with_globality NotReachableInTheNew,[Locality;]); (* 1.13 *)
	     ("propagate_locality",propagate_locality Reachable,[Locality;Reachability;Equality;]); (* 1.12, 1.14 *)
	     ("propagate_locality (with colors)",propagate_locality ReachableInTheNew,[Locality;Reachability';Equality;]); (* 1.12, 1.14 *)
	     ("resolve_data_difference",resolve_data_difference,[Equality;]);
	     ("separation",separation Reachable NotReachable,[Difference;Reachability;NonReachability;]);
	     ("separation (with colors)",separation ReachableInTheNew NotReachableInTheNew,[Difference;Reachability';NonReachability';]);
	     ("non_interfering_cycles",non_interfering_cycles Reachable NotReachable,[Reachability;Difference;NonReachability;Equality;]); (* 1.22 *)
	     ("non_interfering_cycles (with colors)",non_interfering_cycles ReachableInTheNew NotReachableInTheNew,
	      [Reachability';Difference;NonReachability';Equality;]); (* 1.22 *)
	     ("non_reaching_cycles",non_reaching_cycles Reachable NotReachable,[Reachability;Difference;NonReachability;Equality;]); (* 1.22 *)
	     ("non_reaching_cycles (with colors)",non_reaching_cycles ReachableInTheNew NotReachableInTheNew, [Reachability';Difference;NonReachability';Equality;]);
(* 	     ("reaching_order",reaching_order Reachable OneStepReachable NotReachable,[Reachability;ImmediateReachability;(\* Difference; *\)Equality;]); (\* 1.2?? *\) *)
(* 	     ("reaching_order (with colors)",reaching_order ReachableInTheNew OneStepReachableInTheNew NotReachableInTheNew, *)
(* 	      [Reachability';ImmediateReachability';(\* Difference; *\)Equality;]); *)
	     ("check allocation",allocation Reachable,[Equality;Allocation;Reachability;]);
	     ("check allocation (with colors)",allocation ReachableInTheNew,[Equality;Allocation;Reachability';]);
	     ("make deallocation to bottom",deallocation_to_bottom OneStepReachable,[ImmediateReachability;]);
	     ("make deallocation to bottom (with colors)",deallocation_to_bottom OneStepReachableInTheNew,[ImmediateReachability';]);
	   ])
	     ~branching_rules:(
	   [("resolve_difference",resolve_difference,[]); (* 1.21 - keep it here. Important for next-saturation *)
(* 	     ("resolve_reachability",resolve_reachability Reachable NotReachable,[Reachability;NonReachability;]); *)
(* 	     ("resolve_reachability (with colors)",resolve_reachability ReachableInTheNew NotReachableInTheNew,[Reachability';NonReachability';]); *)
	     ("function_successor_reachability",function_successor_reachability Reachable OneStepReachable,[ImmediateReachability;Reachability;Equality;]);  (* 1.16 *)
	     ("function_successor_reachability (with colors)",function_successor_reachability ReachableInTheNew OneStepReachableInTheNew,[ImmediateReachability';Reachability';Equality;]);  (* 1.16 *)
	     ("identify_cycle",identify_cycle Reachable OneStepReachable,[ImmediateReachability;Reachability;Equality;]);  (* 1.17 *)
	     ("identify_cycle (with colors)",identify_cycle ReachableInTheNew OneStepReachableInTheNew,[ImmediateReachability';Reachability';Equality;]);  (* 1.17 *)
	     ("scc",scc Reachable,[Reachability;Equality;]);  (* 1.18 *)
	     ("scc (with colors)",scc ReachableInTheNew,[Reachability';Equality;]);  (* 1.18 *)
	     ("total_reachability",total_reachability Reachable,[Reachability;Equality;]);  (* 1.19 *)
	     ("total_reachability (with colors)",total_reachability ReachableInTheNew,[Reachability';Equality;]);  (* 1.19 *)
	     ("differenciate_dirty_data",differenciate_dirty_data,[Equality;Locality;]); (* 1.20 *)
(* 	     ("separation (if unknown reachability)",separation' Reachable NotReachable,[Reachability;NonReachability;]); *)
(* 	     ("separation (if unknown reachability) (with colors)",separation' ReachableInTheNew NotReachableInTheNew,[Reachability';NonReachability';]); *)
	     ("update_reachability",update_reachability x y,[Reachability;Equality;]); (* 2.3.a *)
	     ("update_reachability_reverse",update_reachability_reverse x y,[Reachability';Equality;]); (* 2.3.b *)
	     ("update_reachability2",update_reachability2 x,[Reachability;Reachability';Equality;]); (* 2.3.c *)
	     ("update_reachability2_reverse",update_reachability2_reverse x,[Reachability;Reachability';Equality;]); (* 2.3.d *)
	     ("update_non_reachability",update_non_reachability x y,[NonReachability;Equality;]); (* 2.4.a *)
	     ("update_non_reachability_reverse",update_non_reachability_reverse x y,[NonReachability';Equality;]); (* 2.4.b *)
	   ]))
(*       end *)
  in
  List.iter P.clean res;
  res
  end

end
