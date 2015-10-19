(*
module C = Constraint
  module R = Rule   
(*///////////////////////////////////////////////////////VECHEV////////////////////////////////////////////////////////////////////////////*)
module Reset : Example.E = struct
	 let name = "Vechev_CAS"	
  let head = Label.global (3,"H",1)
  let tail = Label.global (4,"T",1)
	 let marked = Label.global (0,"marked",1)
   let null = Label.nil
   let free = Label.free
   let pred = Label.local (0, "pred",1)
   let curr = Label.local (1, "curr",1)
   let succ = Label.local (2, "succ",1)
   let x =    Label.local (3, "x",4)
   
	 let intersected_pc = [17;23;9;21;14;22;]
	 let intersect_pc   = [17;23;22]
	 
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
    (new R.atomic 14 12 [(new R.assign_dot_next 14 12 curr pred);]);	
     (new R.atomic 14 12 [(new R.assign_dot_next 14 (-2) curr pred); (new R.data_inequality (-2) (-4) curr 2); (new R.validate_fixed_contains (-4) (-5) true);(new R.validate_fixed_uninsert (-5) (12) curr) ]);	
     (*Out of the loop and add x to the list*)	
			(new R.atomic 12 16 [(new R.less_than 12 16 x curr);]);
    (new R.atomic 12 15 [(new R.less_than 12 (-1) x curr);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) 15 curr);]);
			
    (new R.atomic 12 21 [(new R.data_equality_variable 12 21 x curr);]);
		
    
			(*====================================================CONTAINS====================================================================*)  
   
       (new R.atomic 15 24 [(new R.equal_red 15 (-2) x);(new R.validate_contains_alone (-2) (-3) false);(new R.validate_return (-3) (24) 1 false);]);     (*FALSE*) 
			
		 (new R.atomic 15 24 [(new R.equal_red 15 (-2) x);(new R.validate_undelete (-2) (-3) x true []);(new R.validate_return_new (-3) (24) 3 x false);]);     (*FALSE*) 
    
       	(*====================================================ADD====================================================================*)
			(new R.atomic 16 17 [(new R.dot_next_assign_local 16 17 x curr);]);	
			(new R.atomic 17 18 [(new R.cas_success_set 17 (-1) pred curr 1 x);(new R.validate_insert (-1) 18 x true [
								 {pc=[9;14;16;15];       op = 1(*cnt*);    ret = false; ord = 2(*before*)};
								 {pc=[9;14;16;15];  op = 3(*delete*); ret = false; ord = 2(*before*)}]);	
			  ]);					
    (new R.atomic 17 18 [(new R.cas_fail_set 17 18 pred curr 1 x);]);
    	
			(new R.kill_thread 18 0);	
			
			(*====================================================DELETE==================================================================*)	
			(new R.atomic 21 22 [(new R.assign_dot_next 21 22 succ curr);]);	
		  (new R.atomic 22 23 [(new R.attempt_mark 22 (23) curr succ 1);]);
			(new R.atomic 22 24 [ (new R.attempt_mark_fail 22 24 curr succ 1);]);
			(new R.atomic 23 24 [ (new R.cas_success_set 23 (-1) pred curr 1 succ);(new R.validate_delete_new (-1) 24 curr true []);
			
			]);					
		  (new R.atomic 23 24 [ (new R.cas_fail_set 23 24 pred curr 1 succ);]);		
					
   
	(new R.kill_thread 24 0);
	 ]
end

*)


module C = Constraint
  module R = Rule   
(*///////////////////////////////////////////////////////VECHEV////////////////////////////////////////////////////////////////////////////*)
module Reset : Example.E = struct
	 let name = "Vechev_CAS"	
  let head = Label.global (3,"H",1)
  let tail = Label.global (4,"T",1)
	 let marked = Label.global (0,"marked",1)
   let null = Label.nil
   let free = Label.free
   let pred = Label.local (0, "pred",1)
   let curr = Label.local (1, "curr",1)
   let succ = Label.local (2, "succ",1)
   let x =    Label.local (3, "x",4)
   
	 let intersected_pc = [17;23;9;21;14;22;]
	 let intersect_pc   = [17;23;22]
	 
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
    (new R.atomic 14 12 [(new R.assign_dot_next 14 12 curr pred);]);	
     (new R.atomic 14 12 [(new R.assign_dot_next 14 (12) curr pred); ]);	
     (*Out of the loop and add x to the list*)	
			(new R.atomic 12 16 [(new R.less_than 12 16 x curr);]);
    (new R.atomic 12 15 [(new R.less_than 12 (-1) x curr);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) 15 curr);]);
			
    (new R.atomic 12 21 [(new R.data_equality_variable 12 21 x curr);]);
		
    
			(*====================================================CONTAINS====================================================================*)  
   
      (new R.atomic 15 24 [(new R.validate_contains_local (-2) (-3) x false);(new R.validate_return_new (-3) (24) 1 x false);]);     (*FALSE*) 
			
			(new R.atomic 21 24 [(new R.validate_contains_local (21) (-1) curr true);(new R.validate_return_new (-2) (24) 1 curr true);]);     (*FALSE*) 
			
		  (new R.atomic 15 24 [(new R.validate_undelete (15) (-3) x);(new R.validate_return_new (-3) (24) 3 x false);]);     (*FALSE*) 
    
      (*====================================================ADD====================================================================*)
			(new R.atomic 16 17 [(new R.dot_next_assign_local 16 17 x curr);]);	
			(new R.atomic 17 18 [(new R.cas_success_set 17 (-1) pred curr 1 x);(new R.validate_insert (-1) 18 x true [
								 {pc=[9;14;16;15];       op = 1(*cnt*);    ret = false; ord = 2(*before*)};
								 {pc=[9;14;16;21];       op = 1(*cnt*);    ret = true; ord = 1(*after*)};
								 {pc=[9;14;16;15];  op = 3(*delete*); ret = false; ord = 2(*before*)}]);	
			]);					
      (new R.atomic 17 18 [(new R.cas_fail_set 17 18 pred curr 1 x);]);
    	
			(new R.kill_thread 18 0);	
			
			(*====================================================DELETE==================================================================*)	
			(new R.atomic 21 22 [(new R.assign_dot_next 21 22 succ curr);]);	
		  (new R.atomic 22 23 [(new R.attempt_mark 22 (23) curr succ 1);]);
			(new R.atomic 22 24 [ (new R.attempt_mark_fail 22 24 curr succ 1);]);
    (new R.atomic 23 24 [ (new R.cas_success_set 23 (-1) pred curr 1 succ);(new R.validate_delete (-1) 24 curr true 
                                                                              [{pc=[9;14;16;15];       op = 1(*cnt*);    ret = false; ord = 1(*after*)};
								 {pc=[9;14;16;21];       op = 1(*cnt*);    ret = true; ord = 2(*before*)};
								 {pc=[9;14;16;15];  op = 3(*delete*); ret = false; ord = 1(*after*)};
                                                                              ]);
			
			]);					
		  (new R.atomic 23 24 [ (new R.cas_fail_set 23 24 pred curr 1 succ);]);		
					
   
	(new R.kill_thread 24 0);
	 ]
end