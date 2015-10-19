
module C = Constraint
  module R = Rule   

module Reset : Example.E = struct
   let name = "Treiber"	
   let head = Label.global (3,"H",1)
   let tail = Label.global (4,"T",1)
   let s = Label.global (0,"s",1)
   let null = Label.nil
   let free = Label.free
   let pred = Label.local (0, "p",1)
   let curr = Label.local (1, "c",1)
   let succ = Label.local (2, "s",1)
   let h =    Label.local (3, "h",1)
   let old = Label.local (4, "old",1)
     
   let intersected_pc = [12;2; 13; 18; 22;      43; 47; 50; 54; 44;  86;90 ;  37;39;70;75 ]
   let intersect_pc  = [18; 12; 31; 30; 43; 80; 60;  50; 70; 56; 58; 79; 77]
          
   let initial_predicates  = 
   C.create_unordered_set head tail s
   let predicate_transformers =
     [			 
     (new R.init_thread 0 (3) [|pred;curr;succ;h;old|]);  		  						  				  
	   (new R.atomic 3 7 [(new R.new_cell 3 (-1) h);(new R.data_assign (-1) 7 h 1);]);   
	   (*====================================================ENDLIST======================================================================*)	
	   (new R.atomic 7 12 [(new R.assign 7 12 old head);]);				
     (new R.atomic 12 13 [(new R.dot_next_assign_alone 12 120 h old);(new R.cas_success 120 (-1) head old h);(new R.kill_variable (-1) (-2) old);(new R.validate_insert_unordered (-2) 13 h [86;90;] false)]);	      
     (new R.atomic 12 7 [(new R.cas_fail 12 (-1) head old h);(new R.kill_variable (-1) 7 old);]);		
	   (*====================================================HELP INSERT======================================================================*)
	   (new R.atomic 13 14 [(new R.assign 13 14 pred h);]);		
     (new R.atomic 14 15 [(new R.assign_dot_next 14 15 curr pred);]);	
	   (*while (curr <> null)*)
	   (new R.atomic 15 2 [(new R.in_equality 15 (-1) curr tail);(new R.in_equality (-1) 2 curr null); ]);		    
     (*if curr.state = INV*)
     (new R.atomic 2 16 [(new R.var_data_assign 2 (16) s curr); ]);  
     (new R.atomic 16 17 [(new R.var_equality 16 17 s 16);]);	   (*equal to INV*)
     (new R.atomic 17 18 [(new R.assign_dot_next 17 (18) succ curr);]); 
     (new R.atomic 18 19 [(new R.dot_next_assign (18) 19 pred succ);]);	 
     (new R.atomic 19 15 [(new R.assign 19 (-1) curr succ);(new R.kill_variable (-1) (15) succ)]); 
   
     (new R.atomic 16 20 [(new R.var_inequality 16 (20) s 16);]);   (*not equal to INV*)	
	   (new R.atomic 20 22 [(new R.assign 20 22 pred curr);]);
     (new R.atomic 22 15 [(new R.assign_dot_next 22 (15) curr pred);]);
     
     (new R.atomic 16 31 [(new R.var_equality 16 (-1) s 1(*INS*));(new R.kill_variable (-1) (-2) succ);(new R.color_var_equality (-2) (-3) h curr);(new R.kill_variable (-3) (-4) curr );(new R.kill_variable (-4) (-5)  pred );(new R.kill_variable (-5) 31 succ );]);	(*RETURN FALSE*)  
     

     (new R.atomic 16 30 [(new R.var_equality 16 (-1) s 4(*REM*));(new R.kill_variable (-1) (-2) succ);(new R.color_var_equality (-2) (-3) h curr);(new R.kill_variable (-3) (-4) curr );(new R.kill_variable (-4) (-5)  pred );(new R.kill_variable (-5) 30 succ );]);	(*RETURN TRUE*)	   
     (new R.atomic 16 31 [(new R.var_equality 16 (-1) s 8(*DAT*));(new R.kill_variable (-1) (-2) succ);(new R.color_var_equality (-2) (-3) h curr);(new R.kill_variable (-3) (-4) curr );(new R.kill_variable (-4) (-5)  pred );(new R.kill_variable (-5) 31 succ );]);	(*RETURN FALSE*)             
       
     (new R.atomic 15 30 [(new R.equality 15 (-1) curr tail);(new R.kill_variable (-1) (-2) succ);(new R.color_equality (-2) (-3) h 1);(new R.kill_variable (-3) (-4) curr );(new R.kill_variable (-4) (-5)  pred );(new R.kill_variable (-5) 30 succ ); ]);	(*TRUE*)      
     (new R.atomic 30 32 [(new R.cas_data_success 30 32 h 1 8(*DAT*));]); (*8*)

     (new R.atomic 31 32 [(new R.cas_data_success 31 32 h 1 16);]); (*update to 16 only if data of h is equal to data of curr*)
     (new R.atomic 31 35 [(new R.data_inequality 31 (35) h 1);]); (*16*)	   
     (new R.atomic 30 35 [(new R.data_inequality 30 (35) h 1);]); (*16*)
         
      
     (*===========================Call help remove===========================*)
     (new R.atomic 35 33 [(new R.assign 35 (-1) pred h);(new R.in_equality (-1) 33 pred tail);]);		
   	 (new R.atomic 33 34 [(new R.assign_dot_next 33 34 curr h)]);	
     (*while (curr <> null)*)
       
     (new R.atomic 34 37 [(new R.in_equality 34 (-10) curr tail);(new R.in_equality (-10) 37 curr null);]);		    
     (new R.atomic 37 38 [(new R.var_data_assign 37 38 s curr); ]);
     (*if curr.state = INV*)      
   
     (new R.atomic 38 39 [(new R.var_equality 38 39 s 16);]);			
     (new R.atomic 39 70 [(new R.assign_dot_next 39 (70) succ curr);]);	
	   (new R.atomic 70 71 [(new R.dot_next_assign 70 71 pred succ);]);		
     (new R.atomic 71 34 [(new R.assign 71 (-1) curr succ);(new R.kill_variable (-1) (34) succ)]);
          
     (new R.atomic 38 75 [(new R.var_inequality 38 75 s 16);]);	
     (*curr.key <> k*)
     (new R.atomic 75 76 [(new R.assign 75 76 pred curr);]);
     (new R.atomic 76 34 [(new R.assign_dot_next 76 34 curr pred);]);   
       
	
     (*if curr.key = k*)    
	   (new R.atomic 38 80 [(new R.var_equality 38 (-100) s 4(*REM*));(new R.color_var_equality (-100) (-10) h curr);(new R.kill_variable (-10) (-20) pred );(new R.kill_variable (-20) (-30) curr );(new R.kill_variable (-30) 80 succ );]);	(*RETURN FALSE*)
     (new R.atomic 38 79 [(new R.var_equality 38 799 s 1 (*INS*));(new R.color_var_equality (799) (-2) h curr);(new R.kill_variable (-2) (-3) pred );(new R.kill_variable (-3) 79 succ );]);	
     (new R.atomic 79 80 [(new R.cas_data_success 79 (-20) curr 1 4(*REM*));(new R.kill_variable (-20) (-30) pred );(new R.kill_variable (-30) (-40) curr );(new R.kill_variable (-40) 80 succ );]);(*RETURN TRUE*)
     (new R.atomic 79 80 [(new R.data_inequality 79 (-10) curr 1 );(new R.kill_variable (-10) (-20) pred );(new R.kill_variable (-20) (-30) curr );(new R.kill_variable (-30) 80 succ );]);(*RETURN TRUE*)
    
     (new R.atomic 38 77 [(new R.var_equality 38 (-100) s 8(*DAT*));(new R.color_var_equality (-100) (-101) h curr);(new R.kill_variable (-101) (-102) pred );(new R.kill_variable (-102) 77 succ );]);
     (new R.atomic 77 80 [(new R.data_assign_unordered 77 (-100) curr 16(*INV*));(new R.color_var_equality (-100) (-1) h curr);(new R.kill_variable (-1) (-2) pred );(new R.kill_variable (-2) (-3) curr );(new R.kill_variable (-3) 80 succ );]); (*RETURN TRUE*)
     (new R.atomic 34 80 [(new R.equality 34 (-1) curr tail);(new R.kill_variable (-1) (-2) pred );(new R.kill_variable (-2) (-3) curr );(new R.kill_variable (-3) 80 succ ); ]);	(*RETURN FALSE*)	 	
	   (new R.atomic 80 82 [(new R.data_assign_unordered 80 82 h 16);]);	
               
	(*	 (new R.atomic 35 82 [(new R.data_assign_unordered 35 82 h 16);]);		*)		
     (new R.kill_thread 32 0);   
     (new R.kill_thread 82 0);	      
     
      
     (*==================================================== DELETE======================================================================*)
     (new R.init_thread 0 (40) [|pred;curr;succ;h;old|]);
     (new R.atomic 40 42 [(new R.new_cell 40 (-10) h);(new R.data_assign (-10) 42 h 4);]);   			
     (new R.atomic 42 43 [(new R.assign 42 43 old head);]);	
     (new R.atomic 43 44 [(new R.dot_next_assign_alone 43 41 h old);(new R.cas_success (41) (-20) head old h);(new R.kill_variable (-20) (44) old);]);	
     (new R.atomic 43 42 [(new R.cas_fail 43 (-10) head old h);(new R.kill_variable (-10) (-20) old);(new R.kill_variable (-20) (42) h)]);	  
       
     (new R.atomic 44 45 [(new R.assign 44 45 pred h);]);		
     (new R.atomic 45 46 [(new R.assign_dot_next 45 (46) curr pred);]);	
     (*while (curr <> null)*)
     (new R.atomic 46 47 [(new R.in_equality 46 (-10) curr tail);(new R.in_equality (-10) 47 curr null);]);		
    
     (new R.atomic 47 48 [(new R.var_data_assign 47 48 s curr); ]);
     (*if curr.state = INV*)
     (new R.atomic 48 49 [(new R.var_equality 48 49 s 16);]);			
     (new R.atomic 49 50 [(new R.assign_dot_next (49) (50) succ curr);]);	
     (new R.atomic 50 51 [(new R.dot_next_assign 50 51 pred succ);]);		
     (new R.atomic 51 46 [(new R.assign 51 (-1) curr succ);(new R.kill_variable (-1) 46 succ);]);
      
     (*-----------------------LOOP 1 ---------------------*)
     (new R.atomic 48 53 [(new R.var_inequality 48 53 s 16);]);	   
     (*curr.key <> k*) 
     (new R.atomic 53 54 [(new R.assign 53 54 pred curr);]);
     (new R.atomic 54 46 [(new R.assign_dot_next 54 (46) curr pred);]);      
     (new R.atomic 48 60 [(new R.equality 48 60 curr tail); ]);	 
      
     (*if curr.key = k*)
     (new R.atomic 48 60 [(new R.var_equality 48 (-10) s 4(*REM*));(new R.kill_variable (-10) (-20) pred );(new R.kill_variable (-20) (-30) curr );(new R.kill_variable (-30) 60 succ );]);	(*RETURN FALSE*)	        
     (new R.atomic 48 56 [(new R.var_equality 48 (-10) s 1 (*INS*));(new R.kill_variable (-10) (-20) h );(new R.kill_variable (-20) (-30) pred );(new R.kill_variable (-30) (56) succ )]);	
     (new R.atomic 56 60 [(new R.cas_data_success 56 (-200) curr 1 4(*DAT*)); (new R.validate_delete_unordered (-200) (-20) curr [86;90] false);(new R.kill_variable (-20) (-30) pred );(new R.kill_variable (-30) (-40) curr );(new R.kill_variable (-40) 60 succ );]);(*RETURN TRUE*)
     (new R.atomic 56 60 [(new R.data_inequality 56 (-10) curr 1 );(new R.kill_variable (-10) (-20) pred );(new R.kill_variable (-20) (-30) curr );(new R.kill_variable (-30) 60 succ );]);(*RETURN TRUE*)                                    
     
     (new R.atomic 48 58 [(new R.var_equality 48 (-1) s 8(*DAT*));(new R.kill_variable (-1) (-2) pred );(new R.kill_variable (-2) (-3) succ );(new R.kill_variable (-3) 58 h );]);
     (new R.atomic 58 601 [(new R.data_assign_unordered 58 (-100) curr 16(*INV*));(new R.validate_delete_unordered (-100) 601 curr [86;90] false);]);
			
	   (new R.atomic 601 60 [(new R.kill_variable 601 (-2) pred );(new R.kill_variable (-2) (-3) curr);(new R.kill_variable (-3) 60 succ );]); (*RETURN TRUE*)
     (new R.atomic 46 60 [(new R.equality 46 (-1) curr tail);(new R.kill_variable (-1) (-2) pred );(new R.kill_variable (-2) (-3) curr );(new R.kill_variable (-3) 60 succ); ]);	(*RETURN FALSE*)
                   
     (new R.atomic 60 62 [(new R.data_assign_unordered 60 62 h 16);]);

     (new R.kill_thread 62 0);
      
	
      (*====================================================CONTAINS======================================================================*) 
      (new R.init_thread 0 (83) [|pred;curr;succ;h;old|]);   		
      (new R.atomic 83 84 [(new R.assign 83 84 curr head);]);	
      (new R.atomic 84 86 [(new R.in_equality 84 (-85) curr tail);(new R.in_equality (-85) 86 curr null)]);	
      (new R.atomic 86 87 [(new R.var_data_assign 86 87 s curr); ]);
      (new R.atomic 87 88 [(new R.var_inequality 87 88 s 16 (*INV*));]);
      
       (new R.atomic 88 89 [(new R.var_inequality 88 (-1) s 1 (*INS*));(new R.color_equality (-1) (-2) curr 2 (*INS*));(new R.validate_contains (-2) 89 curr true(*INS*));]);
       (new R.atomic 88 89 [(new R.var_inequality 88 (-1) s 8 (*DAT*));(new R.color_equality (-1) (-2) curr 2 (*INS*));(new R.validate_contains (-2) 89 curr true(*INS*));]);
      
      (new R.kill_thread 88 0);
      (new R.kill_thread 89 0);
      (new R.atomic 87 90 [(new R.var_equality 87 90 s 16 (*INV*));]);	 			
      (new R.atomic 85 90 [(new R.in_equal 85 90 curr curr)]);
      (new R.atomic 90 84 [(new R.assign 90 (-1) old curr);(new R.assign_dot_next (-1) (-2) curr old); (new R.kill_variable (2) 84 old)]);			
      (new R.atomic 84 91 [(new R.equality 84 (-1) curr tail);(new R.in_equality (-1) (-2) curr null);(new R.validate_contains_alone (-2) (-5) false(*INS*));(new R.validate_return (-5) 91 1 false);]);	
      (new R.kill_thread 91 0);	
  
     ]      		
end         
