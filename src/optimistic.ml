module C = Constraint
module R = Rule
(*Optimistic Set lock interleaving*)
module Reset : Example.E = struct
	 let name = "Optimistic"	
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
   let x =    Label.local (5, "x",4)   
	 let initial_predicates  = 
   C.create_set head tail marked 
	 let predicate_transformers  =
	[	
			(*====================================================LOCATE======================================================================*)			
				(new R.init_thread 0 (1) [|pred;curr;succ;temp;node; x|]);      						  				  
	      (new R.atomic 1 7 [
				(new R.new_cell 1 5 x);
        (new R.less_than 5 6 head x);
			  (new R.less_than 6 7 x tail);	
	      ]);	
						
			  (new R.atomic 7 8 [(new R.assign 7 8 pred head);]);	
				(new R.atomic 8 9 [(new R.assign_dot_next 8 9 curr pred); ]);	 
				
				(new R.atomic 9 10 [(new R.less_than 9 10 curr x);]);
				(new R.assign 10 11 pred curr);
        (new R.atomic 11 9 [(new R.assign_dot_next 11 9 curr pred);]); 
				  
				(new R.atomic 9 15 [(new R.less_than 9 15 x curr);]);	              (*For adding*)				
				
				(new R.atomic 15 16 [(new R.lock_acquire_success 15 16 pred 1);]);
				(new R.atomic 16 19 [(new R.lock_acquire_success 16 19 curr 1);]);							  
			  (*====================================================VALIDATE====================================================================*)                  
        
			  (*Validate if pred reach curr and pred is reachable from head*)
				(new R.atomic 19 20 [(new R.assign 19 20 node head);]);	
        		(new R.atomic 20 21 [(new R.less_than 20 (21) node pred);]);	
   (new R.atomic 21 20 [(new R.in_equality 21 (-1) node null);(new R.assign (-1) (-2) temp node); (new R.assign_dot_next (-2) (-3) node temp);(new R.assign (-3) 20 temp free);]);  
   
   
   		  (new R.atomic 20 25 [(new R.equality 20 (-1) node pred);(new R.kill_variable (-1) 25 node);]);
		    (*Check for next equality condition*)
        (new R.atomic 25 26 [(new R.next_equality 25 26 pred curr);]);
   		  (new R.atomic 25 30 [(new R.next_inequality 25 (-1) pred curr);(new R.kill_variable (-1) 30 node);]);
		    (new R.atomic 20 30 [(new R.less_than 20 (-1) pred node);(new R.kill_variable (-1) 30 node);]);	
     
				(*====================================================ADD====================================================================*)   
			  (new R.atomic 26 30 [(new R.dot_next_assign_local 26 27 x curr);
       (new R.dot_next_assign 27 (28) pred x);(new R.validate_insert (28) (-1) x true [];(new R.kill_variable (-1) 30 x););  
         ]);       
  			(new R.atomic 26 27 [(new R.nothing 26 27);]);
   
        (new R.atomic 27 30 [(new R.in_equality 27 (-2) curr tail);(new R.validate_uninsert (-2) 30 curr);]); 
        (new R.atomic 27 30 [(new R.validate_undelete 27 30 x);]); 
  		  (new R.atomic 30 31 [ (new R.lock_release_success 30 (-1) pred 4);(new R.kill_variable (-1) 31 pred)]);
        (new R.atomic 31 32 [(new R.lock_release_success (31) (32) curr 4); ]);
      
        
				(*====================================================CONTAINTS====================================================================*) 									  
   (new R.atomic 27 30 [(new R.in_equality 27 (-2) curr tail);(new R.validate_contains (-2) 30 curr true);]); 
   (new R.atomic 27 30 [(new R.in_equality 27 (-2) curr tail);(new R.validate_contains (-2) 30 x false);]); 
   
				(*====================================================DELETE====================================================================*)   

        (new R.atomic 26 30 [
          (new R.in_equality 26 (-1) curr tail); 							
          (new R.assign_dot_next (-1) (-2) succ curr);
          (new R.dot_next_assign (-2) (-5) pred succ);
          (new R.validate_delete (-5) (-6) curr true []);
          (new R.kill_variable (-6) 30 succ);
        ]); 			 
								
	    (new R.kill_thread 32 0);		
	    (new R.kill_thread 33 0);									    			
                ]
end

