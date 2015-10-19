module C = Constraint
  module R = Rule   
(*////////////////////////////////////////////////////////////////////TREIBER//////////////////////////////////////////////////////////////////////*)

module Reset : Example.E = struct
  let name = "Treibe33r"
  let s = Label.global (3,"S", 1)
  let null = Label.nil
  let free = Label.free
  let x = Label.local (0,"x",1)
  let t = Label.local (1,"t",1)
  let x' = Label.local (0,"x'",1)
  let t' = Label.local (1,"t'",1)
  let initial_predicates  =
  C.create_stack s 
  let predicate_transformers =
   [
    (* ============================ push =============================== *)
   (new R.atomic 0 1 [(new R.init_thread 0 1 [|x;t|]);]);
   (new R.new_cell 1 4 x);
   (new R.assign 4 5 t s);
   (new R.dot_next_assign_local 5 6 x t);
   (new R.atomic 6 (-1) [(new R.cas_fail 6 (-1) s t x);]);
   (new R.kill_variable (-1) 4 t);
   (new R.atomic 6 7 [ (new R.cas_success 6 77 s t x);
   (new R.validate_push 77 7 x);]); (*LINEARIZATION POINT*)
   (new R.kill_thread 7 0);
   (* ============================ pop =============================== *)
   (new R.atomic 0 12 [(new R.init_thread 0 12 [|x';t'|]);]);
   (new R.atomic 12 13 [(new R.assign 12 13 t' s);]);

   (new R.atomic 12 18 [(new R.assign 12 (-1) t' s);(new R.equality (-1) (-2) t' null);(new R.validate_pop_empty (-2) 18 t');]);
	
   (new R.atomic 13 18 [(new R.equality 13 (18) t' null);]);

   (new R.in_equality 13 15 t' null);
   (new R.assign_dot_next 15 17 x' t');
   (*(new R.lin_pop (17) 17 t');*)
   (new R.atomic 17 12 [(new R.cas_fail 17 (-1) s t' x'); 
   (new R.kill_variable (-1) (-2) t');(new R.kill_variable (-2) 12 x');]);		
   (new R.atomic 17 (18) [(new R.cas_success 17 (21) s t' x');
   (new R.validate_pop (21) 18 t');]); (*LINEARIZATION POINT*)
   (new R.kill_thread 18 0);
  ]
end
