module C = Constraint
  module R = Rule   
(*////////////////////////////////////////////////////////////////////TWO LOCK QUEUE//////////////////////////////////////////////////////////////////////*)  
module Reset : Example.E = struct

   let name = "Treiber"

  let qHead = Label.global (3,"H",1)
  let qTail = Label.global (4,"T",1)
  let hLock = Label.global (5,"HLock",3)
  let tLock = Label.global (6,"TLock",3)  
  let null = Label.nil
  let free = Label.free
  let node = Label.local (0,"n",1)
  let next' = Label.local (0,"next'",1)
  let head' = Label.local (1,"h'",1)
    
  let initial_predicates = 
    C.create_twolock_queue qHead qTail hLock tLock 
    
  let predicate_transformers  =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 1 [|node|]);]);
    (new R.new_cell 1 2 node);
    (new R.global_lock 2 3 hLock);  
    (new R.dot_next_assign 3 4 node null);
    (new R.dot_next_assign 4 5 qTail node);
    (new R.atomic 5 7 [(new R.assign 5 6 qTail node); (new R.validate_enqueue 6 7 node);]);
    (new R.global_unlock 7 111 hLock);
		
    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 100 [|next';head';|]);
    (new R.global_lock 100 101 tLock);    
    (new R.atomic 101 102 [(new R.assign 101 102 head' qHead);]);
  
    (new R.atomic 102 104 [(new R.assign_dot_next 102 (-1) next' head');(new R.equality (-1) (-2) next' null);(new R.validate_dequeue_empty (-2) 104 head');]);
		     
    (new R.assign_dot_next 102 104 next' head');
    (new R.in_equality 104 105 next' null);
    (new R.equality 104 107 next' null);
    (new R.global_unlock 107 111 tLock);   
    (new R.atomic 105 106 [(new R.assign 105 (106) qHead next');(new R.validate_dequeue 106 106 next');]);
    (new R.global_unlock 106 111 tLock); 	   
    (* loop *)
    (new R.kill_thread 111 0);
  ]  
end  

