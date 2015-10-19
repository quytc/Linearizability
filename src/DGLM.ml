module C = Constraint
  module R = Rule   
(*////////////////////////////////////////////////////////////////////DGLM QUEUE//////////////////////////////////////////////////////////////////////*)  
module Reset : Example.E = struct

   let name = "DGLM"

   let qHead = Label.global (3,"H",1)
   let qTail = Label.global (4,"T",1)
  let null = Label.nil
  let free = Label.free
  let node = Label.local (0,"n",1)
  let tail = Label.local (1,"t",1)
  let next = Label.local (2,"next",1)
  let next' = Label.local (0,"next'",1)
  let head' = Label.local (1,"h'",1)
  let tail' = Label.local (2,"t'",1)
    
  let intersected_pc = [8;9;10;224; 108]
  let intersect_pc   = [8;9;10;224;108]
    
  let initial_predicates = 
    C.create_queue qHead qTail 
    
  let predicate_transformers =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 1 [|node;tail;next|]);]);
    (new R.new_cell 1 3 node);
    (new R.dot_next_assign 3 4 node null);
    (new R.assign 4 5 tail qTail);
    (new R.assign_dot_next 5 6 next tail);
    (new R.equality 6 7 tail qTail);
    (new R.equality 7 8 next null);  
    (new R.atomic 8 10 [(new R.cas_next_success 8 1011 tail next node);(new R.validate_enqueue 1011 10 node);]);
    (new R.atomic 6 4 [(new R.in_equality 6 (-3) tail qTail);(new R.assign (-3) (-4) tail free);(new R.assign (-4) 4 next free);]);
    (new R.atomic 8 4 [(new R.cas_next_fail 8 (-3) tail next node);(new R.assign (-3) (-4) tail free);(new R.assign (-4) 4 next free);]);
    
    (new R.in_equality 7 9 next null);
    (new R.atomic 9 4 [(new R.cas_success 9 (-3) qTail tail next);(new R.assign (-3) (-4) tail free);(new R.assign (-4) 4 next free);]);
    (new R.atomic 9 4 [(new R.cas_fail 9 (-3) qTail tail next);(new R.assign (-3) (-4) tail free);(new R.assign (-4) 4 next free);]);
    (new R.atomic 10 11 [(new R.cas_success 10 (-2) qTail tail node);(new R.assign (-2) (-3) node free);(new R.assign (-3) (-4) tail free);(new R.assign (-4) 11 next free);]);
    (new R.atomic 10 11 [(new R.cas_fail 10 (-2) qTail tail node);(new R.assign (-2) (-3) node free);(new R.assign (-3) (-4) tail free);(new R.assign (-4) 11 next free);]);
    (* loop *)
    (new R.kill_thread 11 0);
    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next';head';tail'|]);
    (new R.assign 101 103 head' qHead);
    (new R.atomic 103 104 [(new R.assign_dot_next 103 104 next' head');]);
    (*Try linearization*)  
		(new R.atomic 103 1043 [(new R.assign_dot_next 103 1043 next' head');(new R.equality 1043 (-1) tail' head');(new R.equality (-1) (-2) next' null);(new R.validate_dequeue_empty (-2) 1043 head');]);
		
    (new R.atomic 104 105 [(new R.equality 104 105 head' qHead);]);
		(new R.atomic 1043 105 [(new R.equality 1043 105 head' qHead);]);
    (new R.atomic 105 111 [(new R.equality 105 111 next' null);]);
		
    (*if next is not NULL then we need to update qTail before returning to start*)
    (new R.in_equality 105 108 next' null);		
		(new R.atomic 108 222 [(new R.cas_success 108 (-2) qHead head' next');(new R.validate_dequeue (-2) 222 head');]);
		 
	  (new R.assign 222 223 tail' qTail);
		(new R.atomic 223 224 [(new R.equality 223 224 head' tail');]);
		(new R.atomic 224 1110 [(new R.cas_success 224 1110 qTail tail' next');]);
		(new R.atomic 224 1111 [(new R.cas_fail 224 1111 qTail tail' next');]);
		
    (new R.atomic 108 1112 [(new R.cas_fail 108 1112 qHead head' next');]);
    (* loop *)
    (new R.kill_thread 111 0);
		 (new R.kill_thread 1110 0);
		 (new R.kill_thread 1111 0);
		 (new R.kill_thread 1112 0);
  ]  
end  	
