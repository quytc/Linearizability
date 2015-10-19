module C = Constraint
  module R = Rule   
(*////////////////////////////////////////////////////////////////////HSY STACK//////////////////////////////////////////////////////////////////////*)
(*
module Reset : Example.E = struct
  let name = "HSYstack"
  let s = Label.global (3,"S")
  let null = Label.nil
  let free = Label.free
  let x = Label.local (0,"x")
  let t = Label.local (1,"t")
  let x' = Label.local (0,"x'")
  let t' = Label.local (1,"t'")
  let intersected_pc = [6;17;24]
  let intersect_pc   = [17;6;23]
  let initial_predicates =
  let interesting_colors = [||] in
  C.create_stack s interesting_colors 0 0    
  let predicate_transformers =
   [
    (* ============================ push =============================== *)
   (new R.atomic 0 1 [(new R.init_thread 0 1 [|x;t|]);]);
   (new R.new_cell 1 4 x);
   (new R.assign 4 5 t s);
   (new R.dot_next_assign 5 6 x t);
   (new R.atomic 6 4 [(new R.cas_fail 6 4 s t x);]);
   (*Need to colission*)  
   (new R.atomic 6 23 [(new R.cas_fail 6 25 s t x);]);
   (new R.atomic 23 22 [(new R.lin_ex_push_pop 23 22 t');]);    
   (new R.atomic 6 7 [ 
     (new R.cas_success 6 (-1) s t x);
     (new R.lin_push (-1) 7 x);
   ]); (*------------LINEARIZATION POINT------------*)
   (new R.kill_thread 7 0);
		
   (* ============================ pop =============================== *)
   (new R.atomic 0 12 [(new R.init_thread 0 12 [|x';t'|]);]);
   (new R.atomic 12 13 [(new R.assign 12 13 t' s);]);
   
   (new R.atomic 13 18 [(new R.equality 13 18 t' null);]);

   (new R.atomic 13 15 [ (new R.in_equality 13 15 t' null);]);
   (new R.atomic 15 17 [ (new R.assign_dot_next 15 17 x' t');]);

   (new R.atomic 17 22 [(new R.cas_fail 17 22 s t' x');]);
   
   (new R.atomic 17 24 [(new R.cas_fail 17 24 s t' x');]);
         
   (new R.atomic 17 22 [
     (new R.cas_success 17 21 s t' x'); 
     (new R.lin_pop 21 22 t');
   ]);(*------------LINEARIZATION POINT------------*)
   (new R.kill_thread 22 0);
   (new R.kill_thread 23 0);  
   (new R.kill_thread 24 0); 
  ]
end
*)
  
module Reset : Example.E = struct
  let name = "HSYstack"
  let s = Label.global (3,"S")
	let eHead = Label.global (4,"eHead")
	let eTail = Label.global (5,"eTail")
  let null = Label.nil
  let free = Label.free
  let x = Label.local (0,"x")
  let t = Label.local (1,"t")
	let p = Label.local (2,"p")
  let q = Label.local (3,"q")
	let temp = Label.local (4,"temp")
  let x' = Label.local (0,"x'")
  let t' = Label.local (1,"t'")
	let p' = Label.local (2,"p'")
 let q' = Label.local (3,"q'")
 let temp' = Label.local (4,"temp'")
 let intersected_pc = [6;17;2;8;30;11;51;54;56;40]
 let intersect_pc   = [17;6;2;30;9;11;51;54;40;56]
  let initial_predicates =
  let interesting_colors = [||] in
  C.create_elim_stack s eHead eTail interesting_colors 0 0    
  let predicate_transformers =
   [
    (* ============================ push =============================== *)
   (new R.atomic 0 1 [(new R.init_thread 0 1 [|x;t;p;q;temp|]);]);
   (new R.new_cell 1 4 x);
   (new R.assign 4 5 t s);
   (new R.dot_next_assign 5 6 x t);
     (new R.atomic 6 2 [(new R.cas_fail 6 (-1) s t x);(new R.kill_variable (-1) (-2) t);(new R.kill_variable (-2) (2) x)]);
	 (*Elim myself to the array*)
   (new R.atomic 2 8 [(new R.op_assign 2 (-8) p 16);(new R.assign_dot_next (-8) (-1) temp eHead);(new R.dot_next_assign (-1) (-2) p temp);(new R.dot_next_assign (-2) (-3) eHead p);(new R.kill_variable (-3) (8) temp);]);
    
   (*find out the guy who need to get help*)  
     (new R.atomic 8 9  [(new R.get_him_success 8 9 q eHead  p);]);
    
     (new R.atomic 8 22 [(new R.get_him_fail    8 22 q eHead  p);]); 
     
    (new R.atomic 9 10  [(new R.cas_data_elim_success 9 10 p 1 2);]);
    (new R.atomic 9 7  [(new R.cas_data_elim_fail 9 7 p 1 2);]);
   
     (new R.atomic 10 11  [(new R.op_equality   10 11 q 8 (* POP *));]);   
     (new R.atomic 10 7  [(new R.op_inequality 10 7 q 8 (* POP *));]); 
     (*Its ready to do collision between p and q*)	 
     (new R.atomic 11 40  [(new R.cas_data_elim_success 11 40 q 1 1);]);	
    (new R.atomic 11 7  [(new R.cas_data_elim_fail 11 7 q 1 2);]); 
     
   
     (new R.atomic 40 50 [(new R.lin_ex_push_pop 40 50 q);]);    
     
   (new R.atomic 6 7 [ 
     (new R.cas_success 6 (-1) s t x);
     (new R.lin_push (-1) 7 x);
   ]);
   (new R.kill_thread 7 0);
		
   (* ============================ pop =============================== *)
     (new R.atomic 0 12 [(new R.init_thread 0 12 [|x';t';p';q';temp'|]);]);
   (new R.atomic 12 13 [(new R.assign 12 13 t' s);]);
   
   (new R.atomic 13 18 [(new R.equality 13 18 t' null);]);
   (new R.atomic 13 15 [ (new R.in_equality 13 15 t' null);]);
   (new R.atomic 15 17 [ (new R.assign_dot_next 15 17 x' t');]);
   (new R.atomic 17 30 [(new R.cas_fail 17 (-1) s t' x');(new R.kill_variable (-1) (-2) t');(new R.kill_variable (-2) (30) x')]);  
   
	(*Elim myself to the array*)
     (new R.atomic 30 31 [(new R.op_assign 30 (-8) p' 8);(new R.assign_dot_next (-8) (-1) temp' eHead);(new R.dot_next_assign (-1) (-2) p' temp');(new R.dot_next_assign (-2) (-3) eHead p');(new R.kill_variable (-3) (31) temp');]);
     
     
     (new R.atomic 31 51  [(new R.get_him_success 31 51 q' eHead  p');]);
     
     (new R.atomic 31 50 [(new R.get_him_fail    31 50 q' eHead p');]); 
     
     
     (new R.atomic 51 52  [(new R.cas_data_elim_success 51 52 p' 1 2);]);
     
     (new R.atomic 51 50  [(new R.cas_data_elim_fail 51 50 p' 1 2);]);
     
     (new R.atomic 52 54  [(new R.op_equality 52 54 q' 16 (* PUSH *));]);   
     (new R.atomic 52 50  [(new R.op_inequality 52 50 q' 16 (* NOT PUSH *));]);   
     (new R.atomic 54 56  [(new R.cas_data_elim_success 54 56 q' 1 2);]);
     (new R.atomic 54 50  [(new R.cas_data_elim_fail    54 50 q' 1 2);]);
     
     (new R.atomic 56 50 [(new R.lin_ex_push_pop 56 50 p);]);    
     
     
   (new R.atomic 17 22 [
     (new R.cas_success 17 21 s t' x'); 
     (new R.lin_pop 21 22 t');
   ]);(*------------LINEARIZATION POINT------------*)
   
   (new R.kill_thread 22 0);
   (new R.kill_thread 23 0);  
   (new R.kill_thread 24 0);     
   (new R.kill_thread 50 0);  
  ]
end