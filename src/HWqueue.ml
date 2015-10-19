	
module C = Constraint
  module R = Rule   
  
module Reset : Example.E = struct

  let name = "HWqueue"

  let qHead = Label.global (3,"H",1)
  let qBack = Label.global (4,"Back",1)
  let flag = Label.global (0,"flag",1)
  let null = Label.nil
  let free = Label.free
  let i = Label.local (0,"i",1)
  let t = Label.local (1,"t",1)
  let v = Label.local (2,"v",1)
  let i' = Label.local (0,"i'",1)
  let range' = Label.local (1,"range'",1)
  let t' = Label.local (2,"t'",1)
  let v' = Label.local (3,"v'",1)
	      
 let initial_predicates  = C.create_hw_queue qHead  qBack 
  let predicate_transformers =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 2 [(new R.init_thread 0 2 [|i;t;v|]);]);
	  (new R.atomic 2 1 [(new R.validate_call_enqueue 2 1 v)]);
    (*Increase back++*)
    (new R.atomic 1 111 [(new R.reach 1 (-2) qBack null);(new R.assign (-2) (-3) i qBack);(new R.assign_self_dot_next (-3) (111) qBack);]);       
    (*assign value*)
	  (new R.atomic 111 112 [(new R.data_assign 111 (-1) i 2);(new R.color_assign_variable (-1) (-2) i v);(new R.validate_ret_enqueue (-2) 112 i)]); (*LINEARIZATION POINT*)		
    
    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|i';range';t';v'|]);
	  (new R.atomic 101 102 [(new R.assign 101 102 range' qBack);]);
	
	
	  (*Begin the loop from Head to range*)
	  (new R.atomic 102 103 [(new R.assign 102 103 i' qHead);]);
    (new R.atomic 103 104 [(new R.data_exchange 103 (-104) v' i');(new R.data_assign (-104) 109 i' 1); (new R.color_assign (109) 105 i' 1);(new R.validate_ret_dequeue 105 104 v');]);
		(new R.atomic 104 103 [(new R.hq_null_node 104 (-11) v');(new R.reach (-11) (-12) i' range');(new R.assign (-12) (-1) t' i);(new R.assign_dot_next (-1) (-2) t' i');
		(new R.assign (-2) 103 i' t'); ]);
		(new R.atomic 104 113 [(new R.hq_unnull_node 104 113 v');]);				
    (new R.kill_thread 112 0); 
	  (new R.kill_thread 113 0); 
  ]  
end  