module C = Constraint
  module R = Rule   
(*///////////////////////////////////////////////////////VECHEV////////////////////////////////////////////////////////////////////////////*)
module Reset : Example.E = struct
	 let name = "Vechev_DCAS"	
  let head = Label.global (3,"H",1)
  let tail = Label.global (4,"T",1)
	 let marked = Label.global (0,"marked",1)
   let null = Label.nil
   let free = Label.free
   let pred = Label.local (0, "pred",1)
   let curr = Label.local (1, "curr",1)
   let succ = Label.local (2, "succ",1)
   let x =    Label.local (3, "x",4)
   
	 let intersected_pc = [17;23;9;21;14;22;15]
	 let intersect_pc   = [17;23;]
	 
	 let initial_predicates = 
   
   C.create_set head tail marked 
	 let predicate_transformers =
	 [	
			(*====================================================LOCATE======================================================================*)   
			(new R.init_thread 0 (1) [|pred;curr;succ; x|]);      						  				  
	    (new R.atomic 1 7 [
		  (new R.new_cell 1 5 x);
      (new R.less_than 5 6 head x);
			(new R.less_than 6 7 x tail);	
	    ]);	
			(*begin the loop to lock for a position*)				
			(new R.atomic 7 9 [(new R.assign 7 9 pred head);]);				
      (new R.atomic 9 12 [(new R.assign_dot_next 9 12 curr pred); ]);	
						
		  (new R.atomic 12 13 [(new R.less_than 12 13 curr x);]);
			(new R.assign 13 14 pred curr);
      (new R.atomic 14 15 [(new R.assign_dot_next 14 15 curr pred); ]);			  
			
			(new R.atomic 15 1 [(new R.next_equality 15 (-1) curr free);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) 1 curr)]);			
		(new R.atomic 15 1 [(new R.equality 15 (-1) curr free);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) 1 curr)]);			
			
    (new R.atomic 15 12 [(new R.next_inequality 15 (-1) curr free);(new R.in_equality (-1) 12 curr free);]);							  				
			(*Out of the loop and add x to the list*)	
			(new R.atomic 12 16 [(new R.less_than 12 16 x curr);]);
			(new R.atomic 12 21 [(new R.data_equality_variable 12 21 x curr);]);
		 
   		
			(*====================================================CONTAINS====================================================================*)  
	
    (new R.atomic 21 24 [(new R.color_equality 21 (-1) curr 2);(new R.next_inequality (-1) (-2) curr free); (new R.validate_fixed_contains (-2) (-3) true);(new R.validate_fixed_uninsert (-3) (24) curr);]); (*TRUE*)	
    		(new R.atomic 16 24 [(new R.next_equality 16 (-1) pred curr);(new R.equal_red (-1) (-2) x);(new R.validate_fixed_contains (-2) (-3) false);(new R.validate_fixed_undelete (-3) (24) x);]);               (*FALSE*) 
    		(new R.atomic 21 24 [(new R.next_inequality 21 (-1) curr free);(new R.color_equality (-1) (-2) curr 2); (new R.validate_fixed_contains (-2) (-3) true);(new R.validate_fixed_uninsert (-3) (24) curr);]); (*TRUE*)
    
          (*====================================================ADD====================================================================*)
			(new R.atomic 16 17 [(new R.dot_next_assign_local 16 17 x curr);]);	
    (new R.atomic 17 18 [(new R.cas_success_set 17 (-1) pred curr 1 x);(new R.validate_insert (-1) 18 x true []);	
			  ]);					
			(new R.atomic 17 18 [(new R.cas_fail_set 17 18 pred curr 1 x);]);	
			(new R.kill_thread 18 0);	
			
			(*====================================================DELETE==================================================================*)	
			(new R.atomic 21 22 [(new R.assign_dot_next 21 22 succ curr);]);	
    (new R.atomic 22 244 [(new R.dcas_success_set 22 (-1) pred curr succ free);(new R.validate_delete (-1) 24 curr true []);	
			]);					
		  (new R.atomic 22 24 [ (new R.dcas_fail_set 22 24 pred curr succ);]);		
    
   (new R.kill_thread 244 0);
	(new R.kill_thread 24 0);
	 ]
end
