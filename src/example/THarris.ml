module C = Constraint
  module R = Rule        
   (*T HARIS LINKED LIST HELPING                                                                         *)
(*///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
   module Reset : Example.E = struct
	 let name = "THarris"	
  let head = Label.global (3,"H",1)
  let tail = Label.global (4,"T",1)
  let marked = Label.global (0,"marked",1)
   let null = Label.nil
   let free = Label.free
   let t = Label.local (0, "t",1)
   let t_next = Label.local (1, "tn",1)
   let left_node = Label.local (2, "l",1)
   let left_node_next =    Label.local (3, "ln",1)
   let right_node =    Label.local (4, "r",1)
   let right_node_next =    Label.local (5, "rn",1)
   let x =    Label.local (6, "x",4)
	 
	 let initial_predicates  = 
   C.create_set head tail marked  
	 let predicate_transformers =
	[			
		  	(*====================================================SEARCH======================================================================*)
        (new R.init_thread 0 (1) [|t;t_next;left_node;left_node_next;right_node;right_node_next; x|]);      						  				  
	      (new R.atomic 1 7 [
				  (new R.new_cell 1 5 x);
          (new R.less_than 5 6 head x);
			    (new R.less_than 6 7 x tail);	
	       ]);				
        (new R.atomic 7 9 [(new R.assign 7 9 t head);]);			
   (new R.atomic 9 12 [(new R.get_marked_assign_dot_next 9 12 t_next t marked);]);	
   		    (*begin the loop to lock for a position*)
				(new R.atomic 12 15 [
				  (new R.var_inequality 12 (-1) marked 2);
				  (new R.assign (-1) (-2) left_node t);
				  (new R.assign (-2) (15) left_node_next t_next);
				]);
				(new R.atomic 122 15 [
				  (new R.assign (122) (-2) left_node t);
				  (new R.assign (-2) (15) left_node_next t_next);
				]);							
				(new R.atomic 12 15 [(new R.var_equality 12 15 marked 2);]);
				(new R.atomic 15 16 [(new R.assign 15 16 t t_next);]);				
				(new R.atomic 16 20 [(new R.equality 16 20 t tail);]);	
				(new R.atomic 16 17 [(new R.in_equality 16 17 t tail);]);	
 
   (new R.atomic 17 18 [(new R.get_marked_assign_dot_next 17 18 t_next t marked);]);
				(new R.atomic 18 19 [(new R.var_inequality 18 19 marked 2);]);							
   				(new R.atomic 18 15 [(new R.var_equality 18 (15) marked 2); ]);	
   				(new R.atomic 19 122 [(new R.less_than 19 (122) t x);]);	     
				(new R.atomic 19 20 [(new R.less_than 19 20 x t);]);	
				(*(new R.atomic 19 20 [(new R.data_equality_variable 19 20 x t);]);*)
				(new R.atomic 20 21 [
				  (new R.assign 20 (-1) right_node t);	
			    (new R.kill_variable (-1) (-2) t );	
				  (new R.kill_variable (-2) 21 t_next );	
                        ]);
   (new R.atomic 21 22 [(new R.equality 21 22 left_node_next right_node);]);
   
   (new R.atomic 22 1 [(new R.data_equality 22 (-1) right_node 2); (new R.kill_variable (-1) (-2) right_node);(new R.kill_variable (-2) (-3) left_node); (new R.kill_variable (-3) (-4) left_node_next);(new R.kill_variable (-4) (-5) right_node_next);(new R.kill_variable (-5) (-6) t);(new R.kill_variable (-6) (-7) t_next);(new R.kill_variable (-7) (1) x); ]);	  (*search again*)
   
	
   (new R.atomic 22 29 [(new R.data_inequality 22 (-1) right_node 2);(new R.color_inequality (-1) (29) right_node 2);]);(*out of search*)   
   
   (new R.atomic 22 29 [(new R.data_inequality 22 (-1) right_node 2);(new R.color_equality (-1) (-5) right_node 2);(new R.validate_fixed_contains (-5) 29 true);]);(*out of search*)   
   
   (new R.atomic 21 23 [(new R.in_equality 21 23 left_node_next right_node);]);	
   (new R.atomic 23 25 [(new R.cas_success_set 23 (-1) left_node left_node_next 1 right_node); (new R.kill_variable (-1) (25) left_node_next)]);	
   							      	
   (new R.atomic 25 1 [(new R.data_equality 25 (-1) right_node 2);(new R.kill_variable (-1) (-2) right_node);(new R.kill_variable (-2) (-3) left_node); (new R.kill_variable (-3) (-4) left_node_next);(new R.kill_variable (-4) (-5) right_node_next);(new R.kill_variable (-5) (1) x); ]);	                        (*search again*)
   (new R.atomic 25 29 [(new R.data_inequality 25 (-1) right_node 2);(new R.color_inequality (-1) (29) right_node 2);]);(*out of search*)   
   (new R.atomic 25 29 [(new R.data_inequality 25 (-1) right_node 2);(new R.color_equality (-1) (-5) right_node 2);(new R.validate_fixed_contains (-5) 29 true);]);(*out of search*) 
   (new R.atomic 23 1 [(new R.cas_fail_set 23 (-1) left_node left_node_next 1 right_node);(new R.kill_variable (-1) (-2) right_node);(new R.kill_variable (-2) (-3) left_node); (new R.kill_variable (-3) (-4) left_node_next);(new R.kill_variable (-4) (-5) right_node_next);(new R.kill_variable (-5) (1) x);]); (*search again*)								
   
   
   (new R.atomic 23 29 [
     (new R.cas_success_set 23 (-1) left_node left_node_next 1 right_node); 
     		(new R.data_inequality (-1) (-2) right_node 2);
     (new R.canbe_red (-2) (-3) x left_node right_node);
            (new R.validate_fixed_contains (-3) 29 false);
    ]);
   
		    (new R.atomic 29 31 [
				  (new R.kill_variable 29 (-1) left_node_next);
          (new R.kill_variable (-1) 31 right_node_next);	
                          ]);	
          (*====================================================ADD====================================================================*)
			  (new R.atomic 31 32 [(new R.dot_next_assign_local 31 32 x right_node);]);
        	  (new R.atomic 32 33 [(new R.cas_success_set 32 (-1) left_node right_node 1 x);
			  (new R.validate_insert (-1) 33 x true []);
			]);
			  (new R.atomic 32 33 [(new R.cas_fail_set 32 33 left_node right_node 1 x);]);
			  (new R.kill_thread 33 0);				
			
	(*====================================================DELETE==================================================================*)	
			  (new R.atomic 31 34 [(new R.in_equality 31 34 right_node tail);]);
			  (new R.atomic 34 35 [(new R.assign_dot_next 34 35 right_node_next right_node);]);
			  (new R.atomic 35 36 [(new R.data_inequality 35 36 right_node_next 2);]);
			  (new R.atomic 36 37 [(new R.attempt_mark 36 (-1) right_node right_node_next 1);
			  (new R.validate_delete (-1) 37 right_node true []);
	]);			 
			  (new R.atomic 37 40 [(new R.cas_success_set 37 40 left_node right_node 1 right_node_next);]);			
			  (new R.atomic 37 40 [(new R.cas_fail_set 37 40 left_node right_node 1 right_node_next);]);		
   (new R.kill_thread 40 0);		
	 ]
end      