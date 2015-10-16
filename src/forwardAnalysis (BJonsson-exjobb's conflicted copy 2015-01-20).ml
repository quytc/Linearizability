open Printf
exception BreakLoop of int
module C = Constraint
module R = Rule
module Q = Queue

module Algorithm (E : Example.E) = struct

  let debug = false
  let automaton = false

  
  module JS = Joinset.Make(C)
  let clash p = Observer.is_bad (C.observer p)
      
  let verify property = begin

    assert( Debug.print "%s Warning: with Assertions %s" Debug.red Debug.noColor; true );
    let observer = Observer.build property in
    let transformers = E.predicate_transformers observer in   
		let interferers = List.filter R.is_interf transformers in 
    let prios = Observer.nb_priorities observer in
    let intersection_list = ref [||] in	
    let system = JS.create in
    let w = Q.create () in
		let abs_w = Q.create () in
		let working_list_array = ref [||] in
		let abstract_working_list = ref [||] in
    let l =  ref [||] in
		let count = ref 0 in
    let limit = ref 0 in
		let compare_time = ref 0.0000 in
    let new_list = ref [||] in
		let intersected_list = ref [] in
    let new_queue = ref [] in

    let add_to_w p = begin
      if not(C.in_queue p) then begin
        C.set_in_queue p true;
        Q.add p w;
      end;
    end in
        let abs_add_to_w p = begin
        if not(C.in_queue p) then begin
        C.set_in_queue p true;
        Q.add p abs_w;
      end; 
    end in  
    let join_add elt consset = begin
      try
        for n = 0 to Array.length(consset)-1 do
         let (p,res) = C.join_cons elt consset.(n) in
          if res == 0 then begin 
            consset.(n) <- p;
            raise (BreakLoop 4);
          end;   
        done; 
      raise (BreakLoop 5);
      with (BreakLoop 5)  -> Array.append  [|elt|]  consset
        | (BreakLoop 4)  -> consset
    end in

		let join_add_full elt consset = begin
      try
			 for n = 0 to Array.length(consset)-1 do
         let (p,res) = C.join_cons_full elt consset.(n) in
          if res == 0 then begin 
					  consset.(n) <- p;				
				    raise (BreakLoop 400);
          end;  						             
       done; 
      raise (BreakLoop 500);
      with (BreakLoop 500)  ->  Array.append  consset  [|elt|] 
        | (BreakLoop 400)  -> consset
    end in
		
		let join_add_update elt consset = begin
      let new_elt = ref elt in
			try
			 for n = 0 to Array.length(consset)-1 do
         let (p,res) = C.join_cons elt consset.(n) in
          if res == 0 then begin 
						new_elt := p;							
						raise (BreakLoop 400);
          end;  						             
       done; 
      raise (BreakLoop 500);
      with (BreakLoop 500)  -> elt 
        |  (BreakLoop 400)  -> !new_elt
    end in
		
		 let update_add elt list  = begin
			let res = ref 1 in
			let ret = ref [] in 
			for n = List.length(!list)-1 downto 0 do
         if C.compare_world_0 (List.nth !list n) elt <> 0  then                        
             ret :=  (List.nth !list n)::!ret  
				 else
					  begin ret :=  elt::!ret; res := 0; end;
      done;
			(ret,!res)
    end in
		
    let is_pair_pattern p1 p2 l = begin
   
      try
      for i = 0 to Array.length(l)-1 do
        let l1,l2,res,ret = l.(i) in
        let (is_pattern_list1, is_pattern_ret1) = C.is_pattern p1 l1 3 3 in
        let (is_pattern_list2, is_pattern_ret2) = C.is_pattern p2 l2 3 3 in
        if is_pattern_ret1 == 0 && is_pattern_ret2 == 0 then
           raise (BreakLoop 1);
      done;
        raise (BreakLoop 2);
      with (BreakLoop 1) -> 0
      | (BreakLoop 2) -> 1 
    end in
    
    let join_all l = begin       
          let consset = ref [||] in
      for i = 0 to List.length(!l)-1 do
        consset := join_add (List.nth !l i) !consset;					
      done;
     let newList = Array.to_list !consset in
        newList         
    end in
		
		let join_all_full l = begin      
          let consset = ref [||] in
      for i = 0 to (Array.length !l)-1 do			
        consset := join_add_full (!l.(i)) !consset;       
			done;
		 !consset         
    end in
		

    let smart_add elt list = begin      
			let ret = ref [|elt|] in 
			for i = 0 to Array.length !list -1 do
			   if C.compare_world_0 !list.(i) elt <> 0 then
					ret := Array.append [|!list.(i)|] !ret;
			done;      
					!ret    
    end in
		 
		 let smart_add_join elt list = begin     
         
    let set = ref (Array.of_list !list) in
      set := join_add elt !set;
      let newList = Array.to_list !set in
           newList
    end in
		

		
    let working_list =  ref [] in
    let discarded = ref (0) in 
		
		(*//////////////////////////////////////////////////////////////////ABSTRACT POST///////////////////////////////////////////////////////////////////*)
    let rec abs_work _ = begin (* make the call tail-recursive *)    
      let _current = try Some (Q.take abs_w) with Q.Empty -> None in
      match _current with
      | None -> ()
      | Some current -> 		
        C.set_in_queue current false;
       let newcurrent = current in 			
			List.iter (fun (r:R.t) -> List.iter abs_insert_in_system (R.post r newcurrent)) transformers;			
      abs_work ();
    end
		and abs_insert_in_system (predicate:C.t) = begin
		  if clash predicate then raise (C.ClashWithInit predicate);
        try				
					 if  ((C.pc predicate 0) == 0 || (C.pc predicate 0) > 8) then begin
         for n = 0 to (Array.length(!working_list_array))-1 do
          if C.compare_world_0 predicate (!working_list_array.(n)) == 0 then begin  raise (BreakLoop 0) end;          
         done;
				end;
          raise (BreakLoop 3); 
        with (BreakLoop 0)  -> print_string ""
        | (BreakLoop 3)  -> 
					begin   
					abs_add_to_w predicate; working_list_array :=  Array.append !working_list_array [|predicate|];
					(*if (*C.pc predicate 0  ==  32 || C.pc predicate 0  ==  33 || C.pc predicate 0  ==  10034 || C.pc predicate 0  ==  26 || C.pc predicate 0  ==  15*)  then
						 begin new_list := join_add_full predicate !new_list; end;
          *)
					end;								
       end;
    in		
		(*//////////////////////////////////////////////////////////////////NEW ABSTRACT WORK///////////////////////////////////////////////////////////////////*)
	(*Take intersection of every element in l1 to element in l2 then do post and abstract away element in l1*)
				let rec abstract_work i l1 l2 = begin
			  let l1' = ref l1 in
				let p1 = l1.(i) in
				Array.iter (fun p2 ->  let interConstraintList, res =  C.intersection 1 (C.update_scope p1) (C.update_scope p2) 3 3 3 1 in	
					if res then 
						begin
							for k = 0 to (List.length interConstraintList)-1 do
                    let newpredicate = List.nth interConstraintList k in
										let fro = (C.gvar p1) -1 in
                    let til = C.bound p1 in
										C.pure_strengthen newpredicate;
										C.ord_data_from_path newpredicate;	
									(*	print_string " First "; C.print_cons p1;
										print_string " Second "; C.print_cons p2;
								    print_string "\n before pure strengthen ";
											 C.print_merge_cons newpredicate p1 p2;
									*)
										let newpredicate1 = C.clone newpredicate in	
										(*Do post condition for newpredicate*)
										
                    for n = 0 to (List.length interferers)-1 do	
					             let inter_r = List.nth interferers n in
					
					             let quy = R.post_interf inter_r newpredicate in	
								
                       if (List.length quy) > 0 then begin																																												
					             (*Abstract aways the second thread*)
                       for q = 0 to List.length(quy) - 1 do
                        let merge_p = (List.nth quy q) in
								
                        let interf_cons = C.abstract_away merge_p fro til p2 in																							
											  try
                          if C.compare_world_0 interf_cons p1 == 0 then raise (BreakLoop 4)    
													else                   
                           for n = 0 to Array.length(!working_list_array)-1 do
                            if C.compare_world_0 interf_cons !working_list_array.(n) == 0 then begin raise (BreakLoop 4); end;
                           done;
													 for n = 0 to Array.length(!abstract_working_list)-1 do
                            if C.compare_world_0 interf_cons !abstract_working_list.(n) == 0 then begin raise (BreakLoop 4); end;
                           done;
                          raise (BreakLoop 5);
                        with (BreakLoop 4)  -> print_string ""; 
                          | (BreakLoop 5)  -> begin      
                           abstract_working_list := join_add_full interf_cons !abstract_working_list;
													 new_list := join_add_full interf_cons !new_list;
													 working_list_array :=  Array.append  !working_list_array [|interf_cons|] ;
													 (*C.set_in_queue interf_cons false;		
				                   add_to_w interf_cons;	*)
												   if C.pc interf_cons 0 >= 0 then 
														begin (*
															print_string " First "; C.print_cons p1;
															print_string " Second "; C.print_cons p2;
															C.print_merge_cons newpredicate1 p1 p2;
															C.print_merge_cons merge_p p1 p2;
															C.print_cons interf_cons;*)
														end;
                       	 end;																				
					           done;																																																																																																					
                     end;
                    done;																																																																																																															
              done;(*End of loop of interConstraintList*)
						 end;
						) l2;
			let i' = i + 1 in
			if i' < Array.length !l1' then abstract_work i' !l1' l2;
		end in

    (*//////////////////////////////////////////////////////////////////WORK///////////////////////////////////////////////////////////////////*)
    let rec work _ = begin (* make the call tail-recursive *)      
      let _current = try Some (Q.take w) with Q.Empty -> None in
      match _current with
      | None -> ()
      | Some current ->
        C.set_in_queue current false;				
       let newcurrent = current in 
			if C.pc newcurrent 0 == 203 then C.print_cons newcurrent;
      List.iter (fun (r:R.t) -> List.iter insert_in_system (R.post r newcurrent)) transformers;								
      work ();
    end
		 and insert_in_system (predicate:C.t) = begin
      if clash predicate then raise (C.ClashWithInit predicate);
        try
         for n = 0 to (Array.length(!working_list_array))-1 do
          if C.compare_world_0 predicate (!working_list_array.(n)) == 0 then raise (BreakLoop 0)           
         done;
          raise (BreakLoop 3); 
        with (BreakLoop 0)  -> print_string ""
        | (BreakLoop 3)  -> 
					begin   	
					working_list_array :=  Array.append  !working_list_array [|predicate|] ;
				  add_to_w predicate;									
				 if (*add*)C.pc predicate 0  ==  19 || (*delete*)C.pc predicate 0  ==  123 ||  (*delete*)C.pc predicate 0  ==  23 || (*mark*)C.pc predicate 0  ==  2222
				 then begin l := join_add_full predicate !l; end;
          end;								
       end;
	 
in
 let dothejob f = begin
       work ();	
			abstract_working_list := !l;
			for i = 0 to Array.length !abstract_working_list - 1 do
			  print_string "lll"; C.print_cons !abstract_working_list.(i);
			done;
		  let rec dotheabstract f = begin				
		    if !limit == 1 then begin
					print_string " bat dau             ";
          abstract_work 0  !l !abstract_working_list;	       
				  abstract_work 0  !abstract_working_list !l;
					print_string " ket thuc             ";
       end
        else 
					if !limit == 0 then begin
				abstract_work 0 !l !l ;
				(*abstract_work 0 !abstract_working_list !new_list;  *) 
			for i = 0 to Array.length !new_list - 1 do
			   if C.pc !new_list.(i) 0 == 20 then begin print_string "nnnnnnnnnnn"; C.print_cons !new_list.(i); end;
			done; 
        end;      
        l := !new_list;
        new_list := [||];      
        limit :=1; 			
				(* work ();*)
        if Array.length(!l) < 0 then dotheabstract f
      end in 
			       
     dotheabstract 1;
			end in
    (* Initialization *)
    List.iter insert_in_system (E.initial_predicates observer);
   			let org_time = Sys.time () in
		 try
			dothejob ();
      Debug.print "Time of Process: %.2f s | System: %d \n" ((Sys.time ()) -. org_time) (Array.length(!working_list_array));
    with
    | C.Dangling (p,reason) ->
	Debug.print "Dangling pointer: ";
	if !Globals.progress then begin
	  Debug.print "\nin %s\nfrom %s\n" (C.string_of p) (Lazy.force reason);
	  
	end;
	Debug.print "Time: %.2f s | System: %d \n" ((Sys.time ()) -. org_time) (JS.size system);
    | C.NullPointerDereferencing (p,reason) ->
	Debug.print "Null pointer dereferencing: ";
	if !Globals.progress then begin
	  Debug.print "\nin %s\nfrom %s\n" (C.string_of p) (Lazy.force reason);

	end;
	Debug.print "Time: %.2f s | System: %d \n" ((Sys.time ()) -. org_time) (JS.size system);
    | C.FreeDereferencing (p,reason) ->
	Debug.print "Free cell dereferencing: ";
	if !Globals.progress then begin
	  Debug.print "\nin %s\nfrom %s\n" (C.string_of p) (Lazy.force reason);

	end;
	Debug.print "Time: %.2f s | System: %d \n" ((Sys.time ()) -. org_time) (JS.size system);
    | C.Cycle (p,reason) ->
	Debug.print "Cycle creation: ";
	if !Globals.progress then begin
	  Debug.print "\nin %s\nfrom %s\n" (C.string_of p) (Lazy.force reason);
	end;
	Debug.print "Time: %.2f s | System: %d \n" ((Sys.time ()) -. org_time) (JS.size system);
    | C.DoubleFree (p,reason) ->
	Debug.print "Double-free: ";
	if !Globals.progress then begin
	  Debug.print "\nin %s\nfrom %s\n" (C.string_of p) (Lazy.force reason);
	end;
	Debug.print "Time: %.2f s | System: %d \n" ((Sys.time ()) -. org_time) (JS.size system);
    | C.ClashWithInit p ->
	Debug.print "Observed a bad trace: ";
	if !Globals.progress then begin
	  Debug.print "\nin %s\n" (C.string_of p);
	end;
	Debug.print "Time: %.2f s | System: %d \n" ((Sys.time ()) -. org_time) (JS.size system);
    | Invalid_argument reason -> failwith(sprintf "%s Invalid argument: %s %s" Debug.red reason Debug.noColor);
  end

end
    