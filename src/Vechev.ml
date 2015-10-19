module C = Constraint
  module R = Rule   
(*///////////////////////////////////////////////////////VECHEV////////////////////////////////////////////////////////////////////////////*)

module Reset : Example.E = struct
	 let name = "Vechev"	
  let head = Label.global (3,"H",1)
  let tail = Label.global (4,"T",1)
  let marked = Label.global (0,"marked",1)
     let null = Label.nil
     let free = Label.free
     let pred = Label.local (0, "pred",1)
     let curr = Label.local (1, "curr",1)
     let succ = Label.local (2, "succ",1)
     let x =    Label.local (3, "x",4)
   
	   let intersected_pc = [9;12;15]
	   let intersect_pc   = [14;15]
	 
	   let initial_predicates = 
    C.create_set head tail marked 
	   let predicate_transformers =
    [	
    
 (*====================================================LOCATE======================================================================*)

	  (new R.init_thread 0 (1) [|pred;curr;succ; x|]);      						  				  
	  (new R.atomic 1 4 [
	  (new R.new_cell 1 2 x);
    (new R.less_than 2 3 head x);
	  (new R.less_than 3 4 x tail);	
	  ]);	
	  (*begin the loop to lock for a position*)				
	  (new R.atomic 4 9 [(new R.assign 4 9 pred head);]);					
      (new R.atomic 9 12 [(new R.assign_dot_next 9 (-1) curr pred);]); 
      
		(new R.atomic 12 13 [(new R.less_than 12 13 curr x);]);
		(new R.assign 13 9 pred curr);
    (*Out of the locate*)	
    (new R.atomic 12 14 [(new R.less_than 12 14 x curr);]); 
      (new R.atomic 12 17 [(new R.less_than 12 (-1) x curr);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) 17 curr);]);  
		(new R.atomic 12 15 [(new R.data_equality_variable 12 15 x curr);]);          
		(new R.atomic 12 16 [(new R.data_equality_variable 12 16 x curr);]); 		
	  
		(*======================================================ADD====================================================================*)
    
		(*SUCCESS*)
    (new R.atomic 14 18 [	
     (new R.dot_next_unmarked_equality 14 (-2) pred curr);
     (new R.dot_next_assign_local (-2) (-4) x curr);
     (new R.dot_next_assign (-4) (-7) pred x);
      (new R.validate_insert (-7) (-8) x true [{pc=[90;120;170;150];op = 1(*cnt*);ret = false; ord = 2 (*before*)};]);
     (new R.kill_variable (-8) 18  x); 
    ]);
    (*UNSUCCESS*) 		
    (new R.atomic 15 25 [	
     (new R.dot_next_unmarked_equality 15 (-1) pred curr);
      (new R.color_equality (-1) (-3) curr 2); (new R.validate_fixed_uninsert (-3) 25 curr); (*TRUE*)		
    ]);				
    (new R.atomic 14 1 [ 
      (new R.in_dot_next_unmarked_equality 14 (-2) pred curr);
      (new R.kill_variable (-2) (-3) pred);
      (new R.kill_variable (-3) (-4) curr);
      (new R.kill_variable (-4) 1 x);
    ]);	          
			
    (*====================================================DELETE==================================================================*)
     (new R.atomic 15 22 [	
      (new R.dot_next_unmarked_equality 15 (-2) pred curr);
      (new R.data_equality_variable (-2) (-3) x curr);
      (new R.data_assign (-3) (-4) curr 2); 
      (new R.assign_dot_next (-4) (-5) succ curr);
      (new R.dot_next_assign (-5) (-6) pred succ);
			(new R.validate_delete (-6) 22 curr true [
	 							 {pc=[90;120;150;170];    op = 1(*cnt*);    ret = false; ord = 1(*after*)};]);
    ]);
		
    (*UNSUCCESS*) 		
    (new R.atomic 14 23 [	
      (new R.dot_next_unmarked_equality 14 (-1) pred curr);
      (new R.equal_red (-1) (-3) x);(new R.validate_fixed_undelete (-3) 23 x); (*FALSE*)     
    ]);    					
    (new R.atomic 15 1 [(new R.in_dot_next_unmarked_equality 15 (-2) pred curr);
                           (new R.kill_variable (-2) (-3) pred);
      					   (new R.kill_variable (-3) (-4) curr);
        				   (new R.kill_variable (-4) 1 x);
     ]);	
          
					
					
		(*====================================================CONTAINS====================================================================*)
		 (new R.atomic 4 90 [(new R.assign 4 90 pred head);]);						  
		
			(new R.atomic 90 1220 [(new R.assign_dot_next 90 (-1) curr pred);(new R.data_inequality (-1) (-2) curr 2); (new R.color_equality (-1) (-2) curr 2); (new R.validate_fixed_contains (-2) 1220 true);]);	
      (new R.atomic 90 120 [(new R.assign_dot_next 90 (-1) curr pred); (new R.color_inequality (-1) 120 curr 2);]);	
      (new R.atomic 90 120 [(new R.assign_dot_next 90 (-1) curr pred); (new R.data_inequality (-1) 120 curr 2);]);
		 (new R.atomic 120 130 [(new R.less_than 120 130 curr x);]);
		(new R.atomic 1220 130 [(new R.less_than 1220 130 curr x);]);
		 (new R.assign 130 90 pred curr);
     (*Out of the locate*)	
     (new R.atomic 120 170 [(new R.less_than 120 170 x curr);]);  
		 (new R.atomic 1220 170 [(new R.less_than 1220 170 x curr);]);  	
				 (new R.atomic 1220 150 [(new R.data_equality_variable 1220 150 x curr);]);  
		
		(new R.atomic 150 25 [(new R.validate_return_new (150) (25) 1 curr true);]); (*TRUE*)							  
	  (new R.atomic 170 25 [(new R.validate_contains_local 170 (-3) x false);(new R.validate_return_new (-3) (26) 1 x false);]); (*TRUE*)		
   							
								
								
    (new R.kill_thread 18 0);	
    (new R.kill_thread 22 0);

	 ]
end


(*

module Reset : Example.E = struct
	 let name = "Vechev"	
     let head = Label.global (3,"H",1)
     let tail = Label.global (4,"T",1)
	   let marked = Label.global (0,"marked",1)
     let null = Label.nil
     let free = Label.free
     let pred = Label.local (0, "pred",1)
     let curr = Label.local (1, "curr",1)
	   let succ = Label.local (2, "succ",1)
	   let x =    Label.local (3, "x",4)
   
	   let initial_predicates = 
    C.create_set head tail marked 
	   let predicate_transformers =
    [	
    
 (*====================================================LOCATE======================================================================*)

	  (new R.init_thread 0 (1) [|pred;curr;succ; x|]);      	
		(new R.atomic 1 4 [
	  (new R.new_cell 1 2 x);
    (new R.less_than 2 3 head x);
	  (new R.less_than 3 4 x tail);	
	  ]);	
	  (*begin the loop to lock for a position*)				
	  (new R.atomic 4 9 [(new R.assign 4 9 pred head);]);				
    (new R.atomic 9 12 [(new R.assign_dot_next 9 (12) curr pred)]);
		(new R.atomic 12 13 [(new R.less_than 12 13 curr x);]);
		(new R.assign 13 9 pred curr);
    (*Out of the locate*)	
    (new R.atomic 12 14 [(new R.less_than 12 14 x curr);]); 
		(new R.atomic 12 15 [(new R.data_equality_variable 12 15 x curr);]);          
				
	   (*======================================================ADD====================================================================*)
     (*SUCCESS*)
     (new R.atomic 14 18 [	
      (new R.dot_next_unmarked_equality 14 (-2) pred curr);
      (new R.less_than (-2) (-3) x curr);
      (new R.dot_next_assign (-3) (-4) x curr);
      (new R.dot_next_assign (-4) (-7) pred x);
		  (new R.validate_insert (-7) 18 x true [
     						 {pc=[9;12;15;17];    op = 1(*cnt*);    ret = true;  ord = 1(*after*)};]);
     ]);
    (*UNSUCCESS*) 
		
    (new R.atomic 14 25 [	
     (new R.dot_next_unmarked_equality 14 (-1) pred curr);
      (new R.data_equality_variable (-1) (-2) x curr);
      (new R.color_equality (-2) (-3) curr 2); (new R.validate_uninsert (-3) (-4) curr);(new R.validate_return (-4) (25) 2 false); (*TRUE*)		
	
     
    ]);	
			
      (new R.atomic 14 1 [ 
        				   (new R.in_dot_next_unmarked_equality 14 (-2) pred curr);
                           (new R.kill_variable (-2) (-3) pred);
        				   (new R.kill_variable (-3) (-4) curr);
      					   (new R.kill_variable (-4) 1 x);
                          ]);	          
			
    (*====================================================DELETE==================================================================*)
    (*SUCCESS*)
    (new R.atomic 15 22 [	
      (new R.dot_next_unmarked_equality 15 (-2) pred curr);
      (new R.data_equality_variable (-2) (-3) x curr);
      (new R.data_assign (-3) (-4) curr 2); 
      (new R.assign_dot_next (-4) (-5) succ curr);
      (new R.dot_next_assign (-5) (-6) pred succ);
			(new R.validate_delete (-6) 22 curr true [
	 							{pc=[90;120;150;170];    op = 1(*cnt*);    ret = false; ord = 1(*after*)};]);
    ]);
      
     (*UNSUCCESS*) 		
    (new R.atomic 14 23 [	
      (new R.dot_next_unmarked_equality 14 (-1) pred curr);
      (new R.equal_red (-1) (-3) x);(new R.validate_fixed_undelete (-3) 23 x); (*FALSE*)     
    ]);    					
    (new R.atomic 15 1 [(new R.in_dot_next_unmarked_equality 15 (-2) pred curr);
                           (new R.kill_variable (-2) (-3) pred);
      					   (new R.kill_variable (-3) (-4) curr);
        				   (new R.kill_variable (-4) 1 x);
     ]);	
       
		
		
		(*====================================================CONTAINS====================================================================*)
		 (new R.atomic 4 901 [(new R.assign 4 901 pred head);]);		
		 (new R.atomic 901 90 [(new R.validate_early_contains (910) (90) false);]);				  
		
			(new R.atomic 90 1220 [(new R.assign_dot_next 90 (-1) curr pred);(new R.data_inequality (-1) (-2) curr 2); (new R.color_equality (-1) (-2) curr 2); (new R.validate_fixed_contains (-2) 1220 true);]);	
      (new R.atomic 90 120 [(new R.assign_dot_next 90 (-1) curr pred); (new R.color_inequality (-1) 120 curr 2);]);	
      (new R.atomic 90 120 [(new R.assign_dot_next 90 (-1) curr pred); (new R.data_inequality (-1) 120 curr 2);]);
		 (new R.atomic 120 130 [(new R.less_than 120 130 curr x);]);
		(new R.atomic 1220 130 [(new R.less_than 1220 130 curr x);]);
		 (new R.assign 130 90 pred curr);
     (*Out of the locate*)	
     (new R.atomic 120 170 [(new R.less_than 120 170 x curr);]);  
		 (new R.atomic 1220 170 [(new R.less_than 1220 170 x curr);]);  	
				 (new R.atomic 1220 150 [(new R.data_equality_variable 1220 150 x curr);]);  			  
	  (new R.atomic 150 25 [(new R.validate_return_new (150) (25) 1 curr true);]); (*TRUE*)		
    (new R.atomic 170 26 [(new R.validate_return_new (170) (26) 1 x false);]);     (*FALSE*)								
								
										     
    (new R.kill_thread 18 0);
    (new R.kill_thread 19 0);
    (new R.kill_thread 20 0);	
    (new R.kill_thread 22 0);
    (new R.kill_thread 23 0);		 
    (new R.kill_thread 24 0);
    (new R.kill_thread 25 0);
    (new R.kill_thread 26 0);
	 ]
end
*)
