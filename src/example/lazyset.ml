
module C = Constraint
  module R = Rule    

(*
(*LAZY SET in the book lock interleaving OUR METHOD of LP NOT OPTIMAL*)
module Reset : Example.E = struct
	 let name = "LazySet"	
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
   
	 let intersected_pc = [19;15;16;8;11;27;40;26;42;43;44]	
	 let intersect_pc   = [15;16;40;26;30;31]	
	 let initial_predicates  = 
   C.create_set head tail marked 
	 let predicate_transformers =
	[	 
				(new R.init_thread 0 (1) [|pred;curr;succ;temp;node; x|]);   
				(*====================================================LOCATE======================================================================*)								  				  	         	
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
				  
				(new R.atomic 9 15 [(new R.less_than 9 15 x curr);]);	        
				(new R.atomic 15 16 [(new R.lock_acquire_success 15 16 pred 1);]);
				(new R.atomic 16 19 [(new R.lock_acquire_success 16 19 curr 1);]);					
			  
				(*====================================================VALIDATE====================================================================*)                  
			 
			  (*Validate if pred reach curr and pred is reachable from head*)
    
        (new R.atomic 19 26 [(new R.data_equality 19 (-1) pred 1);(new R.data_equality (-1) (-2) curr 1);(new R.next_equality (-2) (-3) pred curr);(new R.validate_undelete (-3) 26 x);]);
        (new R.atomic 19 26 [(new R.data_equality 19 (-1) pred 1);(new R.data_equality (-1) (-2) curr 1);(new R.next_equality (-2) (-3) pred curr);(new R.validate_uninsert (-3) 26 curr);]);
   
				(new R.atomic 19 30 [(new R.data_inequality 30 (-1) pred 1);]);
				(new R.atomic 19 30 [(new R.data_inequality 30 (-1) curr 1);]);
				(new R.atomic 19 30 [(new R.next_inequality 30 (-1) pred curr);]);
        
				(*====================================================ADD====================================================================*)   
			  (new R.atomic 26 30 [(new R.dot_next_assign_local 26 27 x curr);
			  (new R.dot_next_assign 27 (-2) pred x);         
        (new R.validate_insert (-2) (-3) x true [{pc=[42;43;44]; op = 1; ret = false; ord = 2}]);(new R.kill_variable (-3) 30 x);]);(*SUCCESSFUL INSERT*)  			  				
      
				(*====================================================DELETE====================================================================*)   
   		  (new R.atomic 26 40 [(new R.in_equality 26 (-1) curr tail);(new R.data_assign (-1) (-2) curr 2);(new R.validate_delete (-2) 40 curr true [{pc=[421;431;441]; op = 1; ret = false; ord = 1}]) ]); (*SUCCESSFUL DELETE*) 
   
   			(new R.atomic 40 30 [(new R.assign_dot_next 40 (-1) succ curr);(new R.dot_next_assign (-1) (-2) pred succ);(new R.kill_variable (-2) 30 succ);]);     				
    
				(*====================================================CONTAINT==================================================================*)
        
   			(new R.atomic 7 41 [(new R.assign 7 41 curr head);]);
        (new R.atomic 41 42 [(new R.less_than 41 42 curr x);]); 
   			(new R.atomic 42 41 [(new R.assign 42 (-1) temp curr);(new R.assign_dot_next (-1) (-2) curr temp);(new R.kill_variable (-2) 41 temp);]);
   			(new R.atomic 41 43 [(new R.less_than 41 43 x curr);]);      
								
   			(new R.atomic 43 44 [(new R.var_data_assign 43 (-2) marked curr);(new R.color_equality (-2) (-3) curr 2);(new R.var_inequality (-3) (-4) marked 2);(new R.validate_contains (-4) 44 curr true);]); 
	 			(new R.atomic 43 44 [(new R.var_data_assign 43 (-2) marked curr);(new R.color_inequality (-2) (44) curr 2);]); 
   			(new R.atomic 43 44 [(new R.var_data_assign 43 (-2) marked curr);(new R.var_equality (-2) (44) marked 2);]); 
				
			
   			(*It false when LP is put here same as return statement in the algorithm*)				
   
   			(new R.atomic 44 32 [(new R.var_inequality (-1) (-2) marked 2);(new R.validate_return_new (-2) (32) 1 curr true);]); (*RETURN TRUE*)  
   			(new R.atomic 44 32 [(new R.var_inequality (-1) (-2) marked 2);(new R.validate_return_new (-2) (32) 1 curr true);]); (*RETURN TRUE*)    
	 			(new R.atomic 44 32 [(new R.var_equality 44 (-2) marked 2);(new R.validate_contains_local (-2) (32) curr false);]);
				(new R.atomic 43 32 [(new R.nothing 43 32);]);
     		(*Let relesase the lock here*)
   			(new R.atomic 30 31 [(new R.lock_release_success 30 (-1) pred 4);(new R.kill_variable (-1) 31 pred);]);
	 			(new R.atomic 31 32 [(new R.lock_release_success (31) (32) curr 4);]);
	 			(new R.kill_thread 32 0);											    			
]
end 
    *)

module Reset : Example.E = struct
	 let name = "LazySet"	
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
   
	 let intersected_pc = [19;15;16;8;11;27;40;26;42;43;44]	
	 let intersect_pc   = [15;16;40;26;30;31]	
	 let initial_predicates  = 
   C.create_set head tail marked 
	 let predicate_transformers =
	[	 
				(new R.init_thread 0 (1) [|pred;curr;succ;temp;node; x|]);   
				(*====================================================LOCATE======================================================================*)								  				  	         	
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
				  
				(new R.atomic 9 15 [(new R.less_than 9 15 x curr);]);	        
				(new R.atomic 15 16 [(new R.lock_acquire_success 15 16 pred 1);]);
				(new R.atomic 16 19 [(new R.lock_acquire_success 16 19 curr 1);]);					
			  
				(*====================================================VALIDATE====================================================================*)                  
			 
			  (*Validate if pred reach curr and pred is reachable from head*)
    
        (new R.atomic 19 26 [(new R.data_equality 19 (-1) pred 1);(new R.data_equality (-1) (-2) curr 1);(new R.next_equality (-2) (-3) pred curr);(new R.validate_undelete (-3) 26 x);]);
        (new R.atomic 19 26 [(new R.data_equality 19 (-1) pred 1);(new R.data_equality (-1) (-2) curr 1);(new R.next_equality (-2) (-3) pred curr);(new R.validate_uninsert (-3) 26 curr);]);
   
				(new R.atomic 19 30 [(new R.data_inequality 30 (-1) pred 1);]);
				(new R.atomic 19 30 [(new R.data_inequality 30 (-1) curr 1);]);
				(new R.atomic 19 30 [(new R.next_inequality 30 (-1) pred curr);]);
        
				(*====================================================ADD====================================================================*)   
			  (new R.atomic 26 30 [(new R.dot_next_assign_local 26 27 x curr);
			  (new R.dot_next_assign 27 (-2) pred x);         
        (new R.validate_insert (-2) (-3) x true [{pc=[42;43;44]; op = 1; ret = false; ord = 2}]);(new R.kill_variable (-3) 30 x);]);(*SUCCESSFUL INSERT*)  			  				
      
				(*====================================================DELETE====================================================================*)   
   		  (new R.atomic 26 40 [(new R.in_equality 26 (-1) curr tail);(new R.data_assign (-1) (-2) curr 2);(new R.validate_delete (-2) 40 curr true [{pc=[421;431;441]; op = 1; ret = false; ord = 1}]) ]); (*SUCCESSFUL DELETE*) 
   
   			(new R.atomic 40 30 [(new R.assign_dot_next 40 (-1) succ curr);(new R.dot_next_assign (-1) (-2) pred succ);(new R.kill_variable (-2) 30 succ);]);     				
    
				(*====================================================CONTAINT==================================================================*)
        
   			(new R.atomic 7 39 [(new R.assign 7 39 curr head);]);
				(new R.atomic 39 41 [(new R.validate_early_contains (39) (41) false);]);		
				
        (new R.atomic 41 42 [(new R.less_than 41 42 curr x);]); 
   			(new R.atomic 42 41 [(new R.assign 42 (-1) temp curr);(new R.assign_dot_next (-1) (-2) curr temp);(new R.kill_variable (-2) 41 temp);]);
   			(new R.atomic 41 43 [(new R.less_than 41 43 x curr);]);      
								
   			(new R.atomic 43 44 [(new R.var_data_assign 43 (-2) marked curr);(new R.color_equality (-2) (-3) curr 2);(new R.var_inequality (-3) (-4) marked 2);(new R.validate_contains (-4) 44 curr true);]); 
	 			(new R.atomic 43 44 [(new R.var_data_assign 43 (-2) marked curr);(new R.color_inequality (-2) (44) curr 2);]); 
   			(new R.atomic 43 44 [(new R.var_data_assign 43 (-2) marked curr);(new R.var_equality (-2) (44) marked 2);]); 
				
			
   			(*It false when LP is put here same as return statement in the algorithm*)				
   
   			(new R.atomic 44 32 [(new R.var_inequality (-1) (-2) marked 2);(new R.validate_return_new (-2) (32) 1 curr true);]); (*RETURN TRUE*)  
   			(new R.atomic 44 32 [(new R.var_inequality (-1) (-2) marked 2);(new R.validate_return_new (-2) (32) 1 curr true);]); (*RETURN TRUE*)    
	 			(new R.atomic 44 32 [(new R.var_equality 44 (-2) marked 2);(new R.validate_return_new (-2) 32 1 x false);]);
				(new R.atomic 43 32 [(new R.nothing 43 32);]);
     		(*Let relesase the lock here*)
   			(new R.atomic 30 31 [(new R.lock_release_success 30 (-1) pred 4);(new R.kill_variable (-1) 31 pred);]);
	 			(new R.atomic 31 32 [(new R.lock_release_success (31) (32) curr 4);]);
	 			(new R.kill_thread 32 0);											    			
				
					
]
   end 
