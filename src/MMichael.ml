module C = Constraint
module R = Rule   


(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
(*                                                          MICHAEL LINKED LIST                                                                          *)
(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)      
module Reset : Example.E = struct
   let name = "MMichael"	
   let h = Label.global (3,"H",1)
   let t = Label.global (4,"T",1)
   let marked = Label.global (0,"marked",1)
   let null = Label.nil
   let free = Label.free
   let pred = Label.local (0, "p",1)
   let curr = Label.local (1, "c",1)
   let succ = Label.local (2, "s",1)
   let x =    Label.local (3, "x",4)
 
   let intersected_pc = [23;22;20;14;9;11;]
   let intersect_pc   = [23;22;20]

   let initial_predicates  = 
   C.create_set h t marked
	 let predicate_transformers =
	[			  
	   (*====================================================FIND======================================================================*)
    (new R.init_thread 0 (1) [|pred;curr;succ;x|]);      						  				  
   
    (new R.atomic 1 7 [
		(new R.new_cell 1 5 x);
        (new R.less_than 5 6 h x);
	    (new R.less_than 6 7 x t);	
	]);	
   
   (*begin the loop to lock for a position*)				
   (new R.atomic 7 9 [(new R.assign 7 9 pred h);]);				
   (new R.atomic 9 12 [(new R.assign_dot_next 9 12 curr pred); ]);
   (new R.atomic 12 11 [(new R.in_equality 12 11 curr null); ]);		
   (new R.atomic 12 25 [(new R.equality 12 (25) curr null);]);			    
   (new R.atomic 11 8 [(new R.get_marked_assign_dot_next 11 (-8) succ curr marked);(new R.dot_next_unmarked_equality (-8) (-13) pred curr);(new R.var_inequality (-13) (-15) marked 2);
   (new R.less_than (-15) (-1) x curr);(new R.equal_red (-1) (-4) x);(new R.validate_fixed_contains (-4) 8 false)]); (*D3*)
   
   (new R.atomic 11 88 [(new R.get_marked_assign_dot_next 11 (-8) succ curr marked);(new R.dot_next_unmarked_equality (-8) (-13) pred curr);(new R.var_inequality (-13) (-15) marked 2);
   (new R.data_equality_variable (-15) (-1) x curr);(new R.is_color_equality (-1) (-4) curr 2);(new R.validate_fixed_contains (-4) 88 true)]); (*D3*)
   
   (new R.atomic 11 8 [(new R.get_marked_assign_dot_next 11 (-8) succ curr marked);]);
   
   (new R.dot_next_unmarked_equality 8 (-13) pred curr);(new R.var_inequality (-13) (-15) marked 2);
     
   (*Delete the marked node on the way*)			             
   (new R.atomic 8 1 [(new R.next_inequality 8 (-1) pred curr);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) (-3) curr);(new R.kill_variable (-3) (-4) succ);(new R.kill_variable (-4) (-5) x);(new R.kill_ret (-5) (1)); ]); 		 
   (new R.atomic 8 1 [(new R.data_inequality 8 (-1) pred 1);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) (-3) curr);(new R.kill_variable (-3) (-4) succ);(new R.kill_variable (-4) (-5) x);(new R.kill_ret (-5) (1))]); 		    
   (new R.atomic 8 13 [(new R.dot_next_unmarked_equality 8 13 pred curr);]);
 
   (new R.atomic 13 15 [(new R.var_inequality 13 15 marked 2);]);
   (new R.atomic 15 16 [(new R.less_than 15 16 curr x);]);
   (new R.atomic 15 18 [(new R.less_than 15 18 x curr);	]);(*out of search*)								
   (new R.atomic 15 22 [(new R.data_equality_variable 15 (-1) x curr);(new R.kill_variable (-1) 22 x);	]); (*out of search*)
	 
   (new R.atomic 13 14 [(new R.var_equality 13 14 marked 2);]);
   (new R.atomic 14 6 [(new R.cas_success_set 14 (-1) pred curr 1 succ);(new R.kill_variable (-1) 6 curr);]);
   (new R.atomic 6 12 [(new R.assign 6 (-2) curr succ);(new R.kill_variable (-2) 12 succ);]);
   (new R.atomic 14 1 [(new R.cas_fail_set 14 (-1) pred curr 1 succ);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) (-3) curr);(new R.kill_variable (-3) (-4) succ);(new R.kill_variable (-4) (-5) succ);(new R.kill_ret (-5) (1))]);
						
   (new R.atomic 16 12 [
	 (new R.assign 16 (-1) pred curr);
     (new R.assign (-1) (-2) curr succ);
     (new R.kill_variable (-2) (12) succ);
   ]);	
   (*Out of the loop and add x to the list*)	
   (*===================================================ADD======================================================================*)
	  
	 (new R.atomic 18 25 [
	  (new R.validate_return_new 18  45 1 x false  )
   ]);	
	 (new R.atomic 18 25 [
	  (new R.validate_return_new 18  45 1 curr true  )
   ]);		
   (new R.atomic 18 20 [
	  (new R.kill_variable 18 (-1) succ);
	  (new R.dot_next_assign_local (-1) 20 x curr);		
   ]);						
   (new R.atomic 20 25 [
      (new R.cas_success_set 20 (-1) pred curr 1 x);
	  (new R.validate_insert (-1) 25 x true []);
   ]);
   (new R.atomic 20 25 [(new R.cas_fail_set 20 (25) pred curr 1 x);]);	
   (*===================================================REMOVE===================================================================*)	
   (new R.atomic 22 23 [(new R.attempt_mark 22 (-1) curr succ 1);
	  (new R.validate_delete (-1) 23 curr true []);
	]);			
   (new R.atomic 23 25 [(new R.cas_success_set 23 25 pred curr 1 succ);]);			
	  (new R.atomic 23 25 [(new R.cas_fail_set 23 25 pred curr 1 succ);]);
      (new R.kill_thread 25 0);
   ]
   end    
 
 
  