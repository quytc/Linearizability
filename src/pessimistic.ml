module C = Constraint
module R = Rule	
(*Persismistic Set lock interleaving*) 
  module Reset : Example.E = struct
	 let name = "Pessimistic"	
  let head = Label.global (3,"H",1)
  let tail = Label.global (4,"T",1)
	 let marked = Label.global (0,"marked",1)
   let null = Label.nil
   let free = Label.free
   let pred = Label.local (0, "pred",1)
   let curr = Label.local (1, "curr",1)
   let succ = Label.local (2, "succ",1)
   let temp = Label.local (3, "temp",1)
   let node = Label.local (4, "node",1)
   let x =    Label.local (5, "x",1)   
	 let initial_predicates = 
   C.create_set head tail marked 
	 let predicate_transformers =
	[	
			(*====================================================LOCATE======================================================================*)			
   (new R.init_thread 0 (1) [|pred;curr;succ; temp;node;x|]);      						  				  
	      (new R.atomic 1 7 [
				(new R.new_cell 1 5 x);
        (new R.less_than 5 6 head x);
			  (new R.less_than 6 7 x tail);	
	      ]);					
			  (new R.atomic 7 8 [(new R.assign 7 8 pred head);]);	
			 (new R.atomic 8 9 [(new R.lock_acquire_success 8 9 pred 1); ]);	 			
			 	
			  (*begin the loop to lock for a position*)										
        (new R.atomic 9 11 [(new R.assign_dot_next 9 11 curr pred); ]);	 		
				(new R.atomic 11 12 [(new R.lock_acquire_success 11 12 curr 1);]);	                     	
						
		    (new R.atomic 12 13 [(new R.less_than 12 13 curr x);]);
				(new R.atomic 13 14 [(new R.lock_release_success 13 14 pred 4);]);
				(new R.assign 14 15 pred curr);
        (new R.atomic 15 16 [(new R.assign_dot_next 15 16 curr pred); 	]);                       
				(new R.atomic 16 12 [(new R.lock_acquire_success 16 12 curr 1); ]);                      	
		  			
			  (*Out of the loop and add x to the list*)	
				(new R.atomic 12 17 [(new R.less_than 12 17 x curr);]);			
        (new R.atomic 12 22 [(new R.data_equality_variable 12 22 x curr);	]);
			  (*====================================================ADD====================================================================*)
   (new R.atomic 17 24 [(new R.dot_next_assign_lock 17 18 x curr);(new R.dot_next_assign_lock 18 (-1) pred x);(new R.validate_insert (-1) 24 x true []);]); 			     
        (new R.atomic 17 24 [(new R.validate_uninsert (17) 24 curr);]);    
        (new R.atomic 17 24 [(new R.validate_undelete (17) 24 x);]);  
   
			  (*====================================================REMOVE====================================================================*)
			  (new R.atomic 22 23 [(new R.assign_dot_next 22 23 succ curr);]); 
   (new R.atomic 23 24 [(new R.dot_next_assign_lock 23 (-24) pred succ); (new R.validate_delete (-24) 24 curr true [])]);                     	   
        (new R.atomic 24 25 [(new R.lock_release_success 24 (-1) curr 4);(new R.kill_variable (-1) 25 curr);]); 
	      (new R.atomic 25 26 [(new R.lock_release_success 25 26 pred 4);]); 			 
        (new R.kill_thread 26 0);	
  ]
end
  

