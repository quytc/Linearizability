module C = Constraint
  module R = Rule   

module Reset : Example.E = struct
  let name = "HSYstack"
  let s = Label.global (3,"S",1)
  let eHead = Label.global (4,"eHead",2)
  let eTail = Label.global (5,"eTail",2)
  let null = Label.nil
  let free = Label.free
  let x = Label.local (0,"x",4)
  let t = Label.local (1,"t",1)
  let p = Label.local (2,"p",2)
  let q = Label.local (3,"q",2)
  let data = Label.local (4,"data",1)  
  let x' = Label.local (0,"x'",4)
  let t' = Label.local (1,"t'",1)
  let p' = Label.local (2,"p'",2)
  let q' = Label.local (3,"q'",2)
  let data' = Label.local (4,"data'",1)
  let initial_predicates =

  C.create_elim_stack s eHead eTail   
  let predicate_transformers =
   [
    (* ============================ push =============================== *)
     (new R.atomic 0 1 [(new R.init_thread 0 1 [|x;t;p;q;data|]);]);
     (new R.new_cell 1 4 x);
     (new R.assign 4 5 t s);
     (new R.dot_next_assign 5 6 x t);
     (new R.atomic 6 2 [(new R.cas_fail 6 (-1) s t x);(new R.kill_variable (-1) (-2) t);(new R.kill_variable (-2) (2) x)]);
	   (new R.insert_elim 2 8 p eHead);
     (*find out the guy who need to get help*)  
     (new R.atomic 8 9 [(new R.get_him_success 8 9 q eHead  p);]);    
     (new R.atomic 8 7 [(new R.get_him_fail    8 7 q eHead  p);]); 
     
     (new R.atomic 9 10 [(new R.cas_data_success 9 10 p 1 2);]);
     (new R.atomic 9 7  [(new R.cas_data_fail 9 7 p 1 2);]);
   
     (new R.atomic 10 11 [(new R.op_equality   10 11 q 8 (* POP *));]);   
     (new R.atomic 10 7  [(new R.op_inequality 10 7 q 8 (* POP *));]); 
     (*Its ready to do collision between p and q*)	 
     (new R.atomic 11 41 [(new R.cas_data_success 11 40 q 1 2);(new R.validate_ex_push_pop 40 41 data);]);	
     (new R.atomic 11 7  [(new R.cas_data_fail 11 7 q 1 2);]); 
     
   
     (new R.atomic 41 7  [(new R.elim_data_assign 41 7 q data);]); 
     (new R.atomic 41 77 [(new R.elim_data_assign 41 77 q data);]); 
     (new R.atomic 6 7 [ 
     (new R.cas_success 6 (-1) s t x);
     (new R.validate_push (-1) 7 x);
     ]);
     (new R.kill_thread 7 0);
		
     (* ============================ pop =============================== *)
     (new R.atomic 0 12 [(new R.init_thread 0 12 [|x';t';p';q';data'|]);]);
     (new R.atomic 12 13 [(new R.assign 12 13 t' s);]);
     (new R.atomic 12 18 [(new R.assign 12 (-1) t' s);(new R.equality (-1) (-2) t' null);(new R.validate_pop_empty (-2) 18 t');]);
     (new R.atomic 13 15 [ (new R.in_equality 13 15 t' null);]);
     (new R.atomic 15 17 [ (new R.assign_dot_next 15 17 x' t');]);
     (new R.atomic 17 30 [(new R.cas_fail 17 (-1) s t' x');(new R.kill_variable (-1) (-2) t');(new R.kill_variable (-2) (30) x')]);  
   
	   (new R.insert_elim 30 31 p' eHead);    
     (new R.atomic 31 51  [(new R.get_him_success 31 51 q' eHead  p');]);     
     (new R.atomic 31 22 [(new R.get_him_fail    31 22 q' eHead p');]); 
     
     
     (new R.atomic 51 52  [(new R.cas_data_elim_success 51 52 p' 1 2);]);    
     (new R.atomic 51 22  [(new R.cas_data_elim_fail 51 22 p' 1 2);]);     
     (new R.atomic 52 54  [(new R.op_equality 52 54 q' 16 (* PUSH *));]);   
     (new R.atomic 52 22  [(new R.op_inequality 52 22 q' 16 (* NOT PUSH *));]);   
     (new R.atomic 54 22  [(new R.cas_data_elim_success 54 56 q' 1 2);(new R.validate_ex_push_pop 56 22 data');]);
     (new R.atomic 54 22  [(new R.cas_data_elim_fail    54 22 q' 1 2);]);        
     
     (new R.atomic 17 22 [
     (new R.cas_success 17 21 s t' x'); 
     (new R.validate_pop 21 22 t');
     ]);(*------------LINEARIZATION POINT------------*)
   
     (new R.kill_thread 22 0);  
     ]
end  