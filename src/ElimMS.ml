
module C = Constraint
  module R = Rule   
  (*////////////////////////////////////////////////////////////////////ELIMMINATION QUEUE//////////////////////////////////////////////////////////////////////*)
module Reset : Example.E = struct

   let name = "ElimMS"

   let qHead = Label.global (3,"H",1)
   let qTail = Label.global (4,"T",1)
   let eHead = Label.global (5,"eHead",2)
  let null = Label.nil
  let node = Label.local (0,"n",1)
  let tail = Label.local (1,"t",1)
  let next = Label.local (2,"next",1)
  let age  = Label.local (3,"age",1)  
  let p = Label.local (4,"p",2)
  let next' = Label.local (0,"next'",2)
  let head' = Label.local (1,"h'",2)
  let tail' = Label.local (2,"t'",2)
  let p' = Label.local (3,"p'",2)
   let initial_predicates = 
    C.create_elim_queue qHead qTail eHead
    
  let predicate_transformers =
    [
   
		
		(* ===================================================================================== enqueue ======================================================================================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 1 [|node;tail;next; age;p|]);]); 
    (new R.new_cell 1 2 node);
    (new R.assign_dot_next_prev 2 3 age null); (* We need the age here*)
    (new R.dot_next_assign_local 3 4 node null);
    (new R.assign 4 5 tail qTail);
    (new R.assign_dot_next 5 6 next tail);
    (new R.equality 6 7 tail qTail);
		(new R.atomic 6 1 [(new R.in_equality 6 (-2) tail qTail);(new R.kill_variable (-2) (-3) node);(new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) (-5) next);(new R.kill_variable (-5) 1 age);]);      
		(new R.atomic 6 30 [(new R.in_equality 6 (-2) tail qTail);(new R.kill_variable (-2) (-3) node); (new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) 30 next);]);   
    (new R.equality 7 8 next null);  
    (new R.atomic 8 10 [(new R.cas_next_success 8 (-1) tail next node);(new R.validate_enqueue (-1) (-2) node);(new R.kill_variable (-2) (-3) age);(new R.kill_variable (-3) (10) next)]);
    (new R.atomic 8 1 [(new R.cas_next_fail 8 (-2) tail next node);(new R.kill_variable (-2) (-3) node);(new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) (-5) next);(new R.kill_variable (-5) (1) age)]);
       
		(*NEED FOR COLLITION*)       
    (new R.atomic 8 40 [(new R.cas_next_fail 8 (-2) tail next node);(new R.kill_variable (-2) (-3) node); (new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) 301 next); 		
	  (new R.next_equality 301 (-5) age qHead);(new R.kill_variable (-5) 40 age)]);       
		(new R.insert_elim 40 11 p eHead);
		
		(new R.atomic 7 9 [(new R.in_equality 7 (-5) next null);(new R.kill_variable (-5) 9 age);]); (*It is not success here*)		
	 	(new R.atomic 7 30 [(new R.in_equality 7 (-2) next null);(new R.kill_variable (-2) (-3) node); (new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) 30 next);]);   
    (new R.atomic 9 1 [(new R.cas_success 9 (-2) qTail tail next);(new R.kill_variable (-2) (-3) node);(new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) (-5) next);(new R.kill_variable (-5) 1 age);]);
    (new R.atomic 9 1 [(new R.cas_fail 9 (-2) qTail tail next);(new R.kill_variable (-2) (-3) node);(new R.kill_variable (-3) (-4) tail);(new R.kill_variable (-4) (-5) next);(new R.kill_variable (-5) 1 age);]);
    (new R.atomic 10 11 [(new R.cas_success 10 11 qTail tail node);]);
    (new R.atomic 10 11 [(new R.cas_fail 10 11 qTail tail node);]);
    (* loop *)
    (new R.kill_thread 11 0);
		
		
    (* ===================================================================================== dequeue ======================================================================================== *)
    (new R.init_thread 0 101 [|next';head';tail';p'|]);
    (new R.assign 101 102 head' qHead);
    (new R.assign 102 103 tail' qTail);
    (new R.atomic 103 104 [(new R.assign_dot_next 103 104 next' head');]);
    (*Try linearization*)  
    (new R.atomic 104 105 [(new R.equality 104 105 head' qHead);]);
    (new R.atomic 104 111 [(new R.in_equality 104 (-2) head' qHead);
    (new R.kill_variable (-2) (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 111 next');]);
      
     (*If the queue is empty*)  
     (new R.equality 105 106 head' tail');
     (*if next point to Null then come back to start*)
     (new R.atomic 106 111 [(new R.equality 106 (-1) next' null);(new R.kill_variable (-1) (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 111 next');
      ]);
     (*if next is not NULL then we need to update qTail before returning to start*)
     (new R.atomic 106 108 [(new R.in_equality 106 (-1) next' null);(new R.kill_variable (-1) 108 head')]);
    
     (new R.atomic 108 111 [(new R.cas_success 108 (-2) qTail tail' next');
	   (new R.kill_variable (-2) (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 111 next');
     ]);
     (new R.atomic 108 111 [(new R.cas_fail 108 (-2) qTail tail' next');
     (new R.kill_variable (-2) (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 111 next');
     ]);      
     (*If the queue is NOT empty then we can update the Head to next*)
     (new R.atomic 105 110 [(new R.in_equality 105 (-1) head' tail'); (new R.kill_variable (-1) 110 tail');]);
     (new R.atomic 110 111 [(new R.cas_success 110 (-2) qHead head' next');(new R.validate_dequeue (-2) 222 head');  (new R.kill_variable 222 (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 111 next');]);
     (new R.atomic 110 111 [(new R.cas_fail 110 (-2) qHead head' next');       
     (new R.kill_variable (-2) (-3) head');(new R.kill_variable (-3) (-4) tail');(new R.kill_variable (-4) 111 next');
     ]);
     (new R.atomic 110 401 [(new R.cas_fail 110 (-2) qHead head' next');(new R.kill_variable (-2) (-3) head'); (new R.kill_variable (-3) (-4) head');(new R.kill_variable (-4) (-5) tail');(new R.kill_variable (-5) 401 next') ]); 
      
     (new R.atomic 401 402  [(new R.get_him_success 401 402 p' eHead  eHead);]);    
     (new R.atomic 401 111 [(new R.get_him_fail    401 111  p' eHead  eHead);]); 
     (new R.atomic 402 403  [(new R.cas_data_elim_success 402 403 p' 1 2);]);
     (new R.atomic 402 111  [(new R.cas_data_elim_fail 402 111 p' 1 2);]);
     (new R.atomic 403 404  [(new R.op_equality   403 404 p' 16 (* POP *));]);   
     (new R.atomic 403 111  [(new R.op_inequality 403 111 p' 16 (* POP *));]);        
     (new R.atomic 404 111  [(new R.validate_ex_enqueue_dequeue 404 111);]);  
             
     (* loop *)
     (new R.kill_thread 111 0);
  ]  
end  