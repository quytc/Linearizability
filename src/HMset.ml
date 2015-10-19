module C = Constraint
  module R = Rule   
(*IN THE BOOK LOCK FREE*)

  module Reset : Example.E = struct
   let name = "HMset"	
   let h = Label.global (3,"H",1)
   let t = Label.global (4,"T",1)
   let marked = Label.global (0,"marked",1)
   let null = Label.nil
   let free = Label.free
   let pred = Label.local (0, "p",1)
   let curr = Label.local (1, "c",1)
   let succ = Label.local (2, "s",1)
   let x =    Label.local (3, "x",4)
   let temp = Label.local (4, "tmp",1)
	 let intersected_pc = [23;22;20;14;9;10;28;29;31;]
	 let intersect_pc   = [23;22;20]

	 let initial_predicates  = 
  
   C.create_set h t marked
	 let predicate_transformers =
	[			  
			  (new R.init_thread 0 (1) [|pred;curr;succ;x;temp|]);      						  				  
	      (new R.atomic 1 7 [
				  (new R.new_cell 1 5 x);
          (new R.less_than 5 6 h x);
			    (new R.less_than 6 7 x t);	
	      ]);	
								
        (*====================================================FIND======================================================================*)							
			  (*begin the loop to lock for a position*)				
			  (new R.atomic 7 9 [(new R.assign 7 9 pred h);]);				
        (new R.atomic 9 12 [(new R.assign_dot_next 9 12 curr pred); ]);	
				(new R.atomic 12 13 [(new R.get_marked_assign_dot_next 12 13 succ curr marked);]);
			  (*Delete the marked node on the way*)
			  (new R.atomic 13 14 [(new R.var_equality 13 14 marked 2);]);
		    (new R.atomic 14 15 [(new R.cas_success_set 14 15 pred curr 1 succ);]);
   (new R.atomic 15 12  [(new R.assign 15 (-2) curr succ);(new R.kill_variable (-2) 12 succ);]);
			  (new R.atomic 14 24 [(new R.cas_fail_set 14 (-1) pred curr 0 succ);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) (-3) curr);(new R.kill_variable (-3) (-4) succ);(new R.kill_variable (-4) 24 x);]);
		    (*if marked is not seen*)   						
			  (new R.atomic 13 11 [(new R.var_inequality 13 11 marked 2);(new R.var_inequality 13 11 marked 32);]);
			  (new R.atomic 11 16 [(new R.less_than 11 16 curr x);]);
   			  (new R.atomic 11 18 [(new R.less_than 11 (-1) x curr);(new R.kill_ret (-1) 18 );]);			
   (new R.atomic 11 44 [(new R.less_than 11 (-1) x curr);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) (-3) curr);(new R.kill_variable (-3) 44 succ);]);
   (new R.atomic 11 22 [(new R.data_equality_variable 11 (-1) x curr);(new R.kill_ret (-1) 22);]);	
   (new R.atomic 11 33 [(new R.data_equality_variable 11 (-1) x curr);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) 44 succ);]);						
        (new R.atomic 16 12 [
          (new R.assign 16 (-1) pred curr);
          (new R.assign (-1) (-2) curr succ);
           (new R.kill_variable (-2) 12 succ);
				]);				  			
     
    			(*RETURN UNSUCCESS REMOVE*)
				(new R.atomic 44 25 [
      				(new R.validate_undelete  (44) (-2) x); (new R.validate_return_new (-2) 25 3 x false;);
                        ]);	
    
				(*RETURN UNSUCCESS ADD*)
				(new R.atomic 33 25 [
				 (new R.validate_uninsert 33 (-1) curr); (new R.validate_return_new (-1) 25 2 curr false;);
                        ]);	
   
				(*Out of the loop and add x to the list*)			
			  (*===================================================INSERT======================================================================*)
			  (new R.atomic 18 20 [
				 (new R.kill_variable 18 19 succ);
			     (new R.dot_next_assign_local 19 20 x curr);		
				]);						
   (new R.atomic 20 26 [(new R.cas_success_set 20 (-1) pred curr 1 x);(new R.validate_insert (-1) 26 x true [{pc=[9;12;14;44]; op = 3; ret = false; ord = 2}; {pc=[9;12;14;33]; op = 2; ret = false; ord = 1};{pc=[29;28;31;]; op = 1; ret = false; ord = 2}]);]);
			  (new R.atomic 20 26 [(new R.cas_fail_set 20 26 pred curr 1 x);]);		
					
			  (*===================================================REMOVE===================================================================*)			
   (new R.atomic 22 23 [(new R.attempt_mark 22 (-2) curr succ 1);(new R.validate_delete (-2) 23 curr true [{pc=[29;28;31;]; op = 1; ret = false; ord = 1};{pc=[9;12;14;33]; op = 2; ret = false; ord = 2};{pc=[9;12; 14;44]; op = 3; ret = false; ord = 1}]);]);			
		      (new R.atomic 23 24 [(new R.cas_success_set 23 24 pred curr 1 succ)]);				
              (new R.atomic 23 24 [(new R.cas_fail_set 23 24 pred curr 1 succ);]); 
			  (*Kill the variables and go back to the beginning*)			
			  (new R.kill_thread 26 0);
			  (new R.kill_thread 24 0);
              (new R.kill_thread 25 0);				
   
				(*====================================================CONTAINT==================================================================*)
   (new R.atomic 7 27 [(new R.assign 0 27 curr h);]);			
		
        (new R.atomic 27 28 [(new R.less_than 27 28 curr x);]); 
        (new R.atomic 28 27 [(new R.assign 28 (-1) temp curr);(new R.assign_dot_next (-1) (-2) curr temp);(new R.assign (-2) 27 temp free);]);
   (new R.atomic 27 29 [(new R.less_than 27 29 x curr);]);      
				
   (new R.atomic 29 311 [(new R.var_data_assign 29 (-1) marked curr);(new R.var_equality (-1) (-3) marked 1);(new R.validate_contains (-3) 311 curr true);]); 
	  (new R.atomic 29 31 [(new R.var_data_assign 29 (-2) marked curr);(new R.color_equality (-2) (31) curr 1);]); 
        (new R.atomic 29 31 [(new R.var_data_assign 29 (-2) marked curr);(new R.var_equality (-2) (31) marked 2);]); 
      (new R.atomic 29 31 [(new R.var_data_assign 29 (-2) marked curr);(new R.color_equality (-2) (31) curr 32);]); 
          			
    
    (*RETURN TRUE OF CONTAINS*)
   (new R.atomic 311 32 [(new R.var_inequality (-1) (-2) marked 2); new R.validate_return_new (-2) 32 1 curr true;]);
	(*RETURN FALSE OF CONTAINS*)
   (new R.atomic 31 32 [(new R.var_equality 31 (-2) marked 2);(new R.validate_contains_local (-2) (-5) x false);(new R.validate_return_new (-5) 32 1 x false);]);
   (new R.atomic 31 32 [(new R.var_inequality (31) (-2) marked 2);(new R.validate_contains_local (-2) (-5) x false);(new R.validate_return_new (-5) 32 1 x false);]);
 
    
   (new R.kill_thread 31 0);				
	   ]
end


(*
module C = Constraint
  module R = Rule   
(*IN THE BOOK LOCK FREE*)

  module Reset : Example.E = struct
   let name = "HMset"	
   let h = Label.global (3,"H",1)
   let t = Label.global (4,"T",1)
   let marked = Label.global (0,"marked",1)
   let null = Label.nil
   let free = Label.free
   let pred = Label.local (0, "p",1)
   let curr = Label.local (1, "c",1)
   let succ = Label.local (2, "s",1)
   let x =    Label.local (3, "x",4)
   let temp = Label.local (4, "tmp",1)
	 let intersected_pc = [23;22;20;14;9;10;28;29;31;]
	 let intersect_pc   = [23;22;20]

	 let initial_predicates  = 
  
   C.create_set h t marked
	 let predicate_transformers =
	[			  
			  (new R.init_thread 0 (1) [|pred;curr;succ;x;temp|]);      						  				  
	      (new R.atomic 1 7 [
				  (new R.new_cell 1 5 x);
          (new R.less_than 5 6 h x);
			    (new R.less_than 6 7 x t);	
	      ]);	
								
        (*====================================================FIND======================================================================*)							
			  (*begin the loop to lock for a position*)				
			  (new R.atomic 7 9 [(new R.assign 7 9 pred h);]);				
        (new R.atomic 9 12 [(new R.assign_dot_next 9 12 curr pred); ]);	
				(new R.atomic 12 13 [(new R.get_marked_assign_dot_next 12 13 succ curr marked);]);
			  (*Delete the marked node on the way*)
			  (new R.atomic 13 14 [(new R.var_equality 13 14 marked 2);]);
		    (new R.atomic 14 15 [(new R.cas_success_set 14 15 pred curr 1 succ);]);
   (new R.atomic 15 12  [(new R.assign 15 (-2) curr succ);(new R.kill_variable (-2) 12 succ);]);
			  (new R.atomic 14 24 [(new R.cas_fail_set 14 (-1) pred curr 0 succ);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) (-3) curr);(new R.kill_variable (-3) (-4) succ);(new R.kill_variable (-4) 24 x);]);
		    (*if marked is not seen*)   						
			  (new R.atomic 13 11 [(new R.var_inequality 13 11 marked 2);(new R.var_inequality 13 11 marked 32);]);
			  (new R.atomic 11 16 [(new R.less_than 11 16 curr x);]);
   			  (new R.atomic 11 18 [(new R.less_than 11 (-1) x curr);(new R.kill_ret (-1) 18 );]);			
   (new R.atomic 11 44 [(new R.less_than 11 (-1) x curr);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) (-3) curr);(new R.kill_variable (-3) 44 succ);]);
   (new R.atomic 11 22 [(new R.data_equality_variable 11 (-1) x curr);(new R.kill_ret (-1) 22);]);	
   (new R.atomic 11 33 [(new R.data_equality_variable 11 (-1) x curr);(new R.kill_variable (-1) (-2) pred);(new R.kill_variable (-2) 44 succ);]);						
        (new R.atomic 16 12 [
          (new R.assign 16 (-1) pred curr);
          (new R.assign (-1) (-2) curr succ);
           (new R.kill_variable (-2) 12 succ);
				]);				  			
     
    			(*RETURN UNSUCCESS REMOVE*)
				(new R.atomic 44 25 [
      				(new R.validate_undelete  (44) (-2) x); (new R.validate_return_new (-2) 25 3 x false;);
                        ]);	
    
				(*RETURN UNSUCCESS ADD*)
				(new R.atomic 33 25 [
				 (new R.validate_uninsert 33 (-1) curr); (new R.validate_return_new (-1) 25 2 curr false;);
                        ]);	
   
				(*Out of the loop and add x to the list*)			
			  (*===================================================INSERT======================================================================*)
			  (new R.atomic 18 20 [
				 (new R.kill_variable 18 19 succ);
			     (new R.dot_next_assign_local 19 20 x curr);		
				]);						
   (new R.atomic 20 26 [(new R.cas_success_set 20 (-1) pred curr 1 x);(new R.validate_insert (-1) 26 x true [{pc=[9;12;14;44]; op = 3; ret = false; ord = 2}; {pc=[9;12;14;33]; op = 2; ret = false; ord = 1};{pc=[29;28;31;]; op = 1; ret = false; ord = 2}]);]);
			  (new R.atomic 20 26 [(new R.cas_fail_set 20 26 pred curr 1 x);]);		
					
			  (*===================================================REMOVE===================================================================*)			
   (new R.atomic 22 23 [(new R.attempt_mark 22 (-2) curr succ 1);(new R.validate_delete (-2) 23 curr true [{pc=[29;28;31;]; op = 1; ret = false; ord = 1};{pc=[9;12;14;33]; op = 2; ret = false; ord = 2};{pc=[9;12; 14;44]; op = 3; ret = false; ord = 1}]);]);			
		      (new R.atomic 23 24 [(new R.cas_success_set 23 24 pred curr 1 succ)]);				
              (new R.atomic 23 24 [(new R.cas_fail_set 23 24 pred curr 1 succ);]); 
			  (*Kill the variables and go back to the beginning*)			
			  (new R.kill_thread 26 0);
			  (new R.kill_thread 24 0);
              (new R.kill_thread 25 0);				
   
				(*====================================================CONTAINT==================================================================*)
   (new R.atomic 7 277 [(new R.assign 0 277 curr h);]);			
		(new R.atomic 277 27 [(new R.validate_early_contains (277) (27) false);]);	
        (new R.atomic 27 28 [(new R.less_than 27 28 curr x);]); 
        (new R.atomic 28 27 [(new R.assign 28 (-1) temp curr);(new R.assign_dot_next (-1) (-2) curr temp);(new R.assign (-2) 27 temp free);]);
   (new R.atomic 27 29 [(new R.less_than 27 29 x curr);]);      
				
   (new R.atomic 29 311 [(new R.var_data_assign 29 (-1) marked curr);(new R.var_equality (-1) (-3) marked 1);(new R.validate_contains (-3) 311 curr true);]); 
	  (new R.atomic 29 31 [(new R.var_data_assign 29 (-2) marked curr);(new R.color_equality (-2) (31) curr 1);]); 
        (new R.atomic 29 31 [(new R.var_data_assign 29 (-2) marked curr);(new R.var_equality (-2) (31) marked 2);]); 
      (new R.atomic 29 31 [(new R.var_data_assign 29 (-2) marked curr);(new R.color_equality (-2) (31) curr 32);]); 
          			
    
    (*RETURN TRUE OF CONTAINS*)
   (new R.atomic 311 32 [(new R.var_inequality (-1) (-2) marked 2); new R.validate_return_new (-2) 32 1 curr true;]);
	(*RETURN FALSE OF CONTAINS*)
   (new R.atomic 31 32 [(new R.var_equality 31 (-2) marked 2);(new R.validate_return_new (-2) 32 1 x false);]);
   (new R.atomic 31 32 [(new R.var_inequality (31) (-2) marked 2);(*;(new R.validate_contains_local (-2) (-5) x false);*)(new R.validate_return_new (-2) 32 1 x false);]);
 
    
   (new R.kill_thread 31 0);				
	   ]
end

*)
