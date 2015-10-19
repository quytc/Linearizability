module C = Constraint
module R = Rule     
(*////////////////////////////////////////////////////////////////////MS QUEUE//////////////////////////////////////////////////////////////////////*)

module Reset : Example.E = struct

  let name = "MS"

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
  let initial_predicates = C.create_queue qHead qTail
    
  let predicate_transformers =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 1 [|node;tail;next|]);]);
    (new R.new_cell 1 4 node);
    (new R.assign 4 5 tail qTail);
    (new R.assign_dot_next 5 6 next tail);
    (new R.equality 6 7 tail qTail);
    (new R.equality 7 8 next null);  
    (new R.atomic 8 10 [(new R.cas_next_success 8 1011 tail next node);(new R.validate_enqueue 1011 10 node);]);
    (new R.atomic 6 4 [(new R.in_equality 6 (-3) tail qTail);(new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) 4 next);]);
    (new R.atomic 8 4 [(new R.cas_next_fail 8 (-3) tail next node);(new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) 4 next);]);
    
    (new R.in_equality 7 9 next null);
    (new R.atomic 9 4 [(new R.cas_success 9 (-3) qTail tail next);(new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) 4 next);]);
    (new R.atomic 9 4 [(new R.cas_fail 9 (-3) qTail tail next);(new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) 4 next);]);
    (new R.atomic 10 11 [(new R.cas_success 10 (11) qTail tail node);]);
    (new R.atomic 10 11 [(new R.cas_fail 10 (11) qTail tail node);]);
    (* loop *)
    (new R.kill_thread 11 0);
    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next';head';tail'|]);
    (new R.assign 101 102 head' qHead);
    (new R.assign 102 103 tail' qTail);
    (new R.atomic 103 104   [(new R.assign_dot_next 103 104 next' head');]); 
	  (new R.atomic 103 1043  [(new R.assign_dot_next 103 1043 next' head');]); (*LP of EMPTY CANBE HERE*)
		(new R.atomic 1043 1044 [(new R.equality 1043 (-1) tail' head');(new R.equality (-1) (-2) next' null);(new R.validate_dequeue_empty (-2) 1044 head');]);
    (*Try linearization*)  
    (new R.atomic 104 105   [(new R.equality 104 105 head' qHead);]);
    (new R.atomic 104 101   [(new R.in_equality 104 (-2) head' qHead);
		(new R.assign (-2) (-3) head' free);(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 101 next');]);
		(new R.atomic 1044 105  [(new R.equality 1044 105 head' qHead);]);
    (new R.atomic 1044 101  [(new R.in_equality 1044 (-2) head' qHead);
    (new R.kill_variable (-2) (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 101 next');]);
      
    (*If the queue is empty*)  
    (new R.equality 105 106 head' tail');
    (*if next point to Null then come back to start*)
    (new R.atomic 106 111 [(new R.equality 106 (111) next' null);]);
    (*if next is not NULL then we need to update qTail before returning to start*)
    (new R.in_equality 106 108 next' null);
    
    (new R.atomic 108 101 [(new R.cas_success 108 (-2) qTail tail' next');(new R.kill_variable (-2) (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 101 next');]);
    (new R.atomic 108 101 [(new R.cas_fail 108 (-2) qTail tail' next');(new R.kill_variable (-2) (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 101 next');]);      
    (*If the queue is NOT empty then we can update the Head to next*)
    (new R.atomic 105 110 [(new R.in_equality 105 (-1) head' tail'); (new R.kill_variable (-1) 110 tail');]);
  
    (new R.atomic 110 111 [(new R.cas_success 110 (-2) qHead head' next');(new R.validate_dequeue (-2) 111 head');]);
		 
    (new R.atomic 110 101 [(new R.cas_fail 110 (-2) qHead head' next');(new R.kill_variable (-2) (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 101 next');]);
    (*loop*)
    (new R.kill_thread 111 0);
    ]  
end  
  
	