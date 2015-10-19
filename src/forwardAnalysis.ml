
open
  Printf
exception BreakLoop of int
module C = Constraint
module R = Rule
module Q = Queue
module MySet = Set.Make(String)
exception EndLoop of int

module Algorithm (E : Example.E) = struct
  let debug = false
  let automaton = false    
  let verify property example = begin
		C.set_example_name example;
		C.set_property_name property;
    assert( Debug.print "%s Warning: with Assertions %s" Debug.red Debug.noColor; true );
    let transformers = E.predicate_transformers in   
		let test = ref [||] in
		let intersect_set = Array.make 40000 C.emp_constraint in
		let intersect_len = ref 0 in
		let intersected_set = Array.make 40000 C.emp_constraint in
		let intersected_len = ref 0 in      
    let intersect_hash  = Hashtbl.create 50000 in  
    let intersected_hash  = Hashtbl.create 50000 in                                                                        
		let interferers = List.filter R.is_interf transformers in 
		let interferered = List.filter R.is_interfed transformers in 
    let w = Q.create () in
		let working_set = Hashtbl.create 30000 in	
		let working_set1 = Hashtbl.create 30000 in		
		let iter_time = ref 0.0000 in
    let add_to_array len p set = begin
			set.(!len) <- p;
			len := !len + 1;
		end in
    let add_to_w p = begin
      if not(C.in_queue p) then begin
        C.set_in_queue p true;
        Q.add p w;
      end;
    end in
    let discarded = ref (0) in
		
	 (*////////////////////////////////////////////////////////////////ADD_TO_INTERSECT//////////////////////////////////////////////////////////*)	
    let add_to_intersect h p' s = begin
      let p = C.clone p' in
       C.set_interested p true;
      let signature = 	C.signature p in 
			let pc        =   C.pc p 0 in								 
			let oldplist = Hashtbl.find_all h (pc,signature) in
			(*check if the predicate is equal to one of those old predicates*)
			if List.length oldplist = 0 then			
				begin 
					Hashtbl.add h (pc, signature) p; add_to_array intersect_len p intersect_set;
			end
			else
     begin 
              let flag = ref false in
       for i = 0 to List.length oldplist - 1 do
         let oldp1 = List.nth oldplist i in
         if C.interested oldp1 || (C.compare_constraint p oldp1) then flag := true;
       done;		
    if !flag = false then print_string "xxxx";
				for i = 0 to List.length oldplist - 1 do
					 let oldp = List.nth oldplist i in
			
					 if C.interested oldp && not (C.compare_constraint p oldp) then
							begin					
							 let mergep,res = C.merge_constraint p oldp in 
								if res then 
									begin 
										Hashtbl.add h (pc,signature) mergep;
           C.set_interested oldp false;
           C.set_interested mergep true;
           add_to_array intersect_len mergep intersect_set;
            end
						end;
				done;
       (*if not !flag then C.print_cons p;*)
     end;		  
		end in
    (*////////////////////////////////////////////////////////////////ADD_TO_INTERSECT[[[ED]]]//////////////////////////////////////////////////////////*)			
    let add_to_intersected h p s = begin
      let signature = 	C.signature p in 
			let pc        =   C.pc p 0 in								 
			let oldplist = Hashtbl.find_all h (pc,signature) in
			(*check if the predicate is equal to one of those old predicates*)
			if List.length oldplist = 0 then			
				begin 
					Hashtbl.add h (pc, signature) p; add_to_array intersected_len p intersected_set;
			end
			else
			begin 
				for i = 0 to List.length oldplist - 1 do
					 let oldp = List.nth oldplist i in
      if C.interested oldp && not (C.compare_constraint p oldp) then
							begin					
							 let mergep,res = C.merge_constraint p oldp in 
								if res then 
									begin 
										Hashtbl.add h (pc,signature) mergep;
           C.set_interested oldp false;	
           C.set_interested mergep true;									
										add_to_array intersected_len mergep intersected_set;
								end
						end;
				done;
			end;					
		end in
      
    (*//////////////////////////////////////////////////////////////////WORK///////////////////////////////////////////////////////////////////*)
    let rec work _ = begin (* make the call tail-recursive *)    
      let _current = try Some (Q.take w) with Q.Empty -> None in		
      match _current with
      | None -> ()
      | Some current ->
       C.set_in_queue current false;
        if C.pc current 0  = 33330 then begin C.print_cons current; end;			
       if C.not_in_happy current then begin	
          List.iter (fun (r:R.t) -> let new_post_current = R.post r current in 
            List.iter insert_in_system (new_post_current); ) transformers;
        end;
			work ();
		end
    and insert_in_system (predicate:C.t) = begin
      C.clean predicate; 
						let signature = 	C.signature predicate in
						let pc        =   C.pc predicate 0 in		
							  let oldpredicatelist = Hashtbl.find_all working_set (pc,signature) in  
								(*check if the predicate is equal to one of those old predicates*)
								if List.length oldpredicatelist = 0 then			
						    		begin  
											Hashtbl.add working_set (pc,signature) predicate;
											C.set_in_queue predicate false; 
											add_to_w predicate;   										                        
                     
              
              if C.not_in_happy predicate then begin
                      C.compute_successor predicate; 
                List.iter (fun r -> let strength_p = R.strengthen r predicate in List.iter (fun newp -> 
                  if example = "Unordered" && ( C.pc newp 0 = 70 || C.pc newp 0 = 50)  then C.set_pc newp 0 18;
                  if example = "HMset1" && ( C.pc newp 0 = 23)  then C.set_pc newp 0 14;
                  if example = "HMset" && ( C.pc newp 0 = 75)  then C.set_pc newp 0 44;
                  if example = "MMichael" && ( C.pc newp 0 = 23)  then C.set_pc newp 0 14;
                  if (example = "HMset1" && List.mem (C.pc newp 0) [23;22;20;14]) || 
                    (example = "HMset" && List.mem (C.pc newp 0) [44;64;73]) || 
                     (example = "MMichael" && List.mem (C.pc newp 0) [23;22;20;14]) || 
					
					 (example = "Unordered" && (List.mem (C.pc newp 0) [18; 12; 31; 30; 43; 80; 60;  50; 70; 80; 56; 58; 79; 77 ])) ||
             ( example <> "MMichael" && example <> "HMset1" && example <> "Unordered") then
                     add_to_intersect intersect_hash newp intersect_set) strength_p) interferers;																
                List.iter (fun r -> let filter_p = R.filter r predicate in List.iter (fun newp -> if (example = "Unordered" && (List.mem (C.pc newp 0) [12;2; 13; 18; 22;      43; 47; 50; 54; 44;  86;90 ;  37;39;70;75 ])) || example <> "Unordered" then add_to_intersected intersected_hash newp intersected_set) filter_p) interferered;																                    
              end;
              
              
              
              
									  end
						    else
							  begin 
									try
								  for i = 0 to List.length oldpredicatelist - 1 do
								     let oldpredicate = List.nth oldpredicatelist i in 
										 if C.interested oldpredicate then begin
					            if not (C.compare_constraint predicate oldpredicate) then
								      begin	
																					
												let mergepredicate,res = C.merge_constraint predicate oldpredicate in 
									       if res then 
										        begin 
															Hashtbl.add working_set (pc,signature) mergepredicate;
                    C.set_interested oldpredicate false;
                    C.set_interested mergepredicate true;
															C.set_in_queue mergepredicate false; 
										          add_to_w mergepredicate; 
															(*Add to intersection sets*)  
                   
                    if C.not_in_happy mergepredicate then begin	
                       C.compute_successor mergepredicate;														
                      List.iter (fun r -> let strength_p = R.strengthen r mergepredicate in List.iter (fun newp -> 
                        if example = "HMset1" && ( C.pc newp 0 = 23)  then C.set_pc newp 0 14;
                        if example = "HMset" && ( C.pc newp 0 = 75)  then C.set_pc newp 0 44;
                          if example = "MMichael" && ( C.pc newp 0 = 23)  then C.set_pc newp 0 14;
												  if example = "Unordered" && ( C.pc newp 0 = 70 || C.pc newp 0 = 50)  then C.set_pc newp 0 18;
                        if (example = "HMset1" && List.mem (C.pc newp 0) [23;22;20;14]) || 
                           (example = "HMset" && List.mem (C.pc newp 0) [44;64;73]) || 
                          (example = "MMichael" && List.mem (C.pc newp 0) [23;22;20;14]) || 
													
													 (example = "Unordered" && (List.mem (C.pc newp 0) [18; 12; 31; 30; 43; 80; 60;  50; 70; 80; 56; 58; 79; 77 ])) ||
													 ( example <> "MMichael" && example <> "HMset1" && example <> "Unordered") then add_to_intersect intersect_hash newp intersect_set) strength_p) interferers;
                                               
                      List.iter (fun r -> let filter_p = R.filter r mergepredicate in List.iter (fun newp ->   if (example = "Unordered" && (List.mem (C.pc newp 0) [12;2; 13; 18; 22;      43; 47; 50; 54; 44;  86;90 ;  37;39;70;75 ])) || example <> "Unordered" then  add_to_intersected intersected_hash newp intersected_set) filter_p) interferered;																
                    end;	
										
																					
																																
																																																						 
															(*raise the condidition here to finish the loop*)
															raise (EndLoop 0);
									        end;												
								      end
											else
												raise (EndLoop 1)
														end
											else if (C.compare_constraint predicate oldpredicate) then raise (EndLoop 1);
			             done;
									 raise (EndLoop 2)
									with
									| (EndLoop 2) -> ()					
									| (EndLoop 0) -> ()
									| (EndLoop 1) -> ()	
							end								 							  		
        end									 
in
let compute_inference p p1 p2 = begin 
	let fro = (C.gvar p1) -1 in
  let til = C.bound p1 in
  C.pure_strengthen p;
  let pp = C.clone p in
	(*HW queue*)
	for i = 0 to (List.length interferers)-1 do	
			let inter_r = List.nth interferers i in		
			let post_constraintlist = R.post_interf inter_r p in						
      if (List.length post_constraintlist) > 0 then begin																																											
				(*Abstract aways the second thread*)					 
			  for j = 0 to List.length(post_constraintlist) - 1 do						
       let merge_p = (List.nth post_constraintlist j) in	
       
							 let interf_cons = C.abstract_away merge_p fro til p2 in
						  
       if not (C.compare_constraint interf_cons p2) then 
         begin  
           insert_in_system (interf_cons); 
           
         end; 
				
       if C.pc p1 0 = 152222 then							
        begin 
          
              print_string " first "; C.print_cons p1;
          print_string " second "; C.print_cons p2;   
            (*
              print_string " merge "; 
                
							C.print_merge_cons pp p1 p2;       
            *)
							print_string " MERGE "; C.print_merge_cons pp p1 p2; 
              print_string " MERGE POST "; C.print_merge_cons merge_p p1 p2;
							
              C.print_cons interf_cons; 
            end
						
	      done;		
  end;
 done; 
end in
let intersection s1 s2 i1 i2 j1 j2  = begin		
	for i = i1 to i2 - 1 do
		for j = j1 to j2 - 1 do
    let p1, p2 = s1.(i), s2.(j) in
    if C.pc p1 0 = 5422 then C.print_cons p1;
		if C.interested p1 && C.interested p2 && C.observer p1 = C.observer p2 then begin 
				begin 
			    (*     
			  let sp1,sp2 = if example = "DGLM" then begin C.start_point p1, C.start_point p2; end else 3,3 in
        let org_time = Sys.time () in 
        let interConstraintList, res = if sp1 = sp2 then C.do_intersection p1 p2 sp1 sp1 sp1 1 else [],false in
        iter_time := !iter_time +. ((Sys.time ()) -. org_time);
        *)
      
       let interConstraintList, res =  C.do_full_intersection p1 p2 1  in 
      
    
             if res then begin
								(*Compute inference*)	
								List.iter(fun x -> compute_inference x p1 p2) interConstraintList;
					   end
				end
			end
		done;
	done;
end in

let dotheabstractjob f = begin 
		let old_intersect_len,old_intersected_len = !intersect_len,!intersected_len in
		intersection intersect_set intersected_set 0 !intersect_len 0 !intersected_len;
		let new_intersect_len,new_intersected_len = !intersect_len,!intersected_len in
		let rec dotheabstractloop old_intersect_len old_intersected_len new_intersect_len new_intersected_len = 
			begin
		    intersection intersect_set intersected_set old_intersect_len new_intersect_len 0 new_intersected_len;
        intersection intersect_set intersected_set 0 old_intersect_len old_intersected_len new_intersected_len;
        work ();	  
		    let old_intersect_len = new_intersect_len in
		    let new_intersect_len = !intersect_len in
		    let old_intersected_len = new_intersected_len in
		    let new_intersected_len = !intersected_len in
		    if old_intersect_len <> new_intersect_len || old_intersected_len <> new_intersected_len then
           dotheabstractloop old_intersect_len old_intersected_len new_intersect_len new_intersected_len;      
		end in
		dotheabstractloop old_intersect_len old_intersected_len new_intersect_len new_intersected_len;
end	in	
  let dothejob f = begin
      work ();		   
    dotheabstractjob ();	
 end in
    (* Initialization *)
    List.iter insert_in_system (E.initial_predicates);
						let org_time = Sys.time () in  
		 try
			dothejob ();
			
			
	
(*///////////////////////////////////////////////////////////////////////////////TEST/////////////////////////////////////////////////////////////////////////////////////////////////////////*)			
(*////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)	
for i = 0 to !intersected_len - 1  do
  if C.pc intersected_set.(i) 0 = 43335 then  begin C.print_cons intersected_set.(i); print_string "\n";  end;
done;	
for i = 0 to !intersect_len - 1 do
  if C.pc intersect_set.(i) 0 = 2222  then begin  print_int (C.pc intersect_set.(i) 0); C.print_cons intersect_set.(i); print_string "\n"; end;
done;							
		
	 Debug.print "\n Time of Process: %.2f s | System: %d \n " ((Sys.time ()) -. org_time) (Hashtbl.length(working_set)) ;

	 print_string (C.result);
	 print_string "\n";
 
   
   with
    | C.Dangling (p,reason) ->
	Debug.print "Dangling pointer: ";
	if !Globals.progress then begin
	  Debug.print "" ;	  
	end;
	Debug.print "";
    | C.NullPointerDereferencing (p,reason) ->
	Debug.print "Null pointer dereferencing: ";
	if !Globals.progress then begin
	  Debug.print "";
	end;
	Debug.print "";
    | C.FreeDereferencing (p,reason) ->
	Debug.print "Free cell dereferencing: ";
	if !Globals.progress then begin
	  Debug.print "";
	end;
end
end


(*
open Printf
exception BreakLoop of int
module C = Constraint
module R = Rule
module Q = Queue
module MySet = Set.Make(String)
exception EndLoop of int

module Algorithm (E : Example.E) = struct
  let debug = false
  let automaton = false    
  let verify property example = begin
	  print_string "here is the example name_ "; print_string example;
		C.set_example_name example;
    assert( Debug.print "%s Warning: with Assertions %s" Debug.red Debug.noColor; true );
    let transformers = E.predicate_transformers in   
		let test = ref [||] in
		let intersect_set = Array.make 40000 C.emp_constraint in
		let intersect_len = ref 0 in
		let intersected_set = Array.make 40000 C.emp_constraint in
		let intersected_len = ref 0 in      
    let intersect_hash  = Hashtbl.create 50000 in  
    let intersected_hash  = Hashtbl.create 50000 in                                                                        
    let interferers = List.filter R.is_interf transformers in
    let interferered = List.filter R.is_interfed transformers in 
    let w = Q.create () in
		let working_set = Hashtbl.create 30000 in	
		let fixed1 = ref [||] in
    let fixed2 = ref [||] in
    let fixed3 = ref [||] in
		let fixed11 = ref [||] in
		let fixed12 = ref [||] in
		let working_set1 = Hashtbl.create 30000 in		
		let inter_time = ref 0.0000 in
    let add_to_array len p set = begin
			set.(!len) <- p;
			len := !len + 1;
		end in
    let add_to_w p = begin
      if not(C.in_queue p) then begin
        C.set_in_queue p true;
        Q.add p w;
      end;
    end in
    let discarded = ref (0) in
		(*////////////////////////////////////////////////////////////////ADD_TO_INTERSECT//////////////////////////////////////////////////////////*)	
    let add_to_intersect h p' s = begin
      let p = C.clone p' in
       C.set_interested p true;
      let signature = 	C.signature p in 
			let pc        =   C.pc p 0 in								 
			let oldplist = Hashtbl.find_all h (pc,signature) in
			(*check if the predicate is equal to one of those old predicates*)
			if List.length oldplist = 0 then			
				begin 
					Hashtbl.add h (pc, signature) p; add_to_array intersect_len p intersect_set;
			end
			else
     begin 
              let flag = ref false in
       for i = 0 to List.length oldplist - 1 do
         let oldp1 = List.nth oldplist i in
         if C.interested oldp1 || (C.compare_constraint p oldp1) then flag := true;
       done;		
    if !flag = false then C.print_cons p;
				for i = 0 to List.length oldplist - 1 do
					 let oldp = List.nth oldplist i in
			
					 if C.interested oldp && not (C.compare_constraint p oldp) then
							begin					
							 let mergep,res = C.merge_constraint p oldp in 
								if res then 
									begin 
										Hashtbl.add h (pc,signature) mergep;
           C.set_interested oldp false;
           C.set_interested mergep true;
           add_to_array intersect_len mergep intersect_set;
            end(*
               else   C.print_cons p; (*add_to_array intersect_len p intersect_set;*)*)
						end;
				done;
       (*if not !flag then C.print_cons p;*)
     end;		  
		end in
    (*////////////////////////////////////////////////////////////////ADD_TO_INTERSECT[[[ED]]]//////////////////////////////////////////////////////////*)			
    let add_to_intersected h p s = begin
      let signature = 	C.signature p in 
			let pc        =   C.pc p 0 in								 
			let oldplist = Hashtbl.find_all h (pc,signature) in
			(*check if the predicate is equal to one of those old predicates*)
			if List.length oldplist = 0 then			
				begin 
					Hashtbl.add h (pc, signature) p; add_to_array intersected_len p intersected_set;
			end
			else
			begin 
				for i = 0 to List.length oldplist - 1 do
					 let oldp = List.nth oldplist i in
      if C.interested oldp && not (C.compare_constraint p oldp) then
							begin					
							 let mergep,res = C.merge_constraint p oldp in 
								if res then 
									begin 
										Hashtbl.add h (pc,signature) mergep;
           C.set_interested oldp false;	
           C.set_interested mergep true;									
										add_to_array intersected_len mergep intersected_set;
								end(*
								else begin C.print_cons oldp; print_string " second "; C.print_cons p(*add_to_array intersected_len p intersected_set*);end;*)
						end;
				done;
			end;					
		end in
      
      
    
    (*//////////////////////////////////////////////////////////////////WORK///////////////////////////////////////////////////////////////////*)
       let rec work _ = begin (* make the call tail-recursive *)    
      let _current = try Some (Q.take w) with Q.Empty -> None in		
      match _current with
      | None -> ()
      | Some current ->
       C.set_in_queue current false;
        if C.pc current 0 = 5899 then begin C.print_cons current; end;		
       if C.not_in_happy current then begin	
          List.iter (fun (r:R.t) -> let new_post_current = R.post r current in 
            List.iter insert_in_system (new_post_current); ) transformers;
        end;
			work ();
		end
    and insert_in_system (predicate:C.t)  = begin 
			let m = true in
     C.clean predicate;
     let signature = 	C.signature predicate in
						let pc        =   C.pc predicate 0 in		
							  let oldpredicatelist = Hashtbl.find_all working_set (pc,signature) in  
								(*check if the predicate is equal to one of those old predicates*)
								if List.length oldpredicatelist = 0 then			
						    		begin  
											Hashtbl.add working_set (pc,signature) predicate;
											C.set_in_queue predicate false; 
											add_to_w predicate;   								
											
																										
										 (*==============================================================================================================================*)	
              (*
							if C.not_in_happy predicate then begin
                      C.compute_successor predicate; 
                List.iter (fun r -> let strength_p = R.strengthen r predicate in List.iter (fun newp -> 
                  if (List.mem (C.pc newp 0) [18; 12;  31; 30; 43; 80; 60;  50; 70; 56; 58; 79; 77]) 
                     then 
                       begin  if C.pc newp 0 = 70 || C.pc newp 0 = 50  then C.set_pc newp 0 18;  if C.pc newp 0 = 56  then C.set_pc newp 0 79;  if C.pc newp 0 = 58  then C.set_pc newp 0 77;  if C.pc newp 0 = 80  then C.set_pc newp 0 60;
                         add_to_intersect intersect_hash newp intersect_set end) strength_p) interferers;																
                List.iter (fun r -> let filter_p = R.filter r predicate in List.iter (fun newp -> 
                  if (List.mem (C.pc newp 0) [12;2; 13; 18; 22;      43; 47; 50; 54; 44;  86;90 ;  37;39;70;75 ])  then   
                               add_to_intersected intersected_hash newp intersected_set) filter_p) interferered;														                    
              end;
              *)
							 if C.not_in_happy predicate then begin
                      C.compute_successor predicate; 
                List.iter (fun r -> let strength_p = R.strengthen r predicate in List.iter (fun newp -> 
									    if example = "Unordered" && ( C.pc newp 0 = 70 || C.pc newp 0 = 50)  then C.set_pc newp 0 18;
									    if (example = "HMset1" && List.mem (C.pc newp 0) [23;22;20]) || 
									    (example = "MMichael" && List.mem (C.pc newp 0) [23;22;20]) || 
											(example = "THarris" && ((C.pc newp 0 <> 37) )) ||
											(example = "Unordered" && (List.mem (C.pc newp 0) [18; 12; 31; 30; 43; 80; 60;  50; 70; 80; 56; 58; 79; 77 ])) ||
											(example <> "THarris" && example <> "MMichael" && example <> "HMset1" && example <> "Unordered") then add_to_intersect intersect_hash newp intersect_set) strength_p) interferers;																
                List.iter (fun r -> let filter_p = R.filter r predicate in List.iter (fun newp -> if (example = "Unordered" && (List.mem (C.pc newp 0) [12;2; 13; 18; 22;      43; 47; 50; 54; 44;  86;90 ;  37;39;70;75 ])) || example <> "Unordered" then add_to_intersected intersected_hash newp intersected_set) filter_p) interferered;																                    
              end;
							
							
							
									  end
						    else
							  begin 
									try
								  for i = 0 to List.length oldpredicatelist - 1 do
								     let oldpredicate = List.nth oldpredicatelist i in 
            if C.interested oldpredicate then begin
					            if not (C.compare_constraint predicate oldpredicate) then
								      begin	
																					
												let mergepredicate,res = C.merge_constraint predicate oldpredicate in 
												
												if res &&  C.pc predicate 0 = 202 then begin C.print_cons predicate; C.print_cons oldpredicate;  end;
												
									       if res then 
										        begin 
															Hashtbl.add working_set (pc,signature) mergepredicate;
                              C.set_interested oldpredicate false;
															C.set_in_queue mergepredicate false; 
                    C.set_interested mergepredicate true;
                    add_to_w mergepredicate;
															
															
															(*==============================================================================================================================*)																															
     (*
					if C.not_in_happy mergepredicate then begin	
                       C.compute_successor mergepredicate;														
                      List.iter (fun r -> let strength_p = R.strengthen r mergepredicate in List.iter (fun newp -> 
                        if (List.mem (C.pc newp 0) [18; 12; 31; 30; 43; 80; 60;  50; 70; 56; 58; 79; 77 ])    
                            then begin if C.pc newp 0 = 70 || C.pc newp 0 = 50  then C.set_pc newp 0 18;  if C.pc newp 0 = 56  then C.set_pc newp 0 79;  if C.pc newp 0 = 58  then C.set_pc newp 0 77;  if C.pc newp 0 = 80  then C.set_pc newp 0 60; 
														add_to_intersect intersect_hash newp intersect_set end) strength_p) interferers;
                                               
                      List.iter (fun r -> let filter_p = R.filter r mergepredicate in List.iter (fun newp ->  
                       					 if (List.mem (C.pc newp 0) [12;2; 13; 18; 22;      43; 47; 50; 54; 44;  86;90 ;  37;39;70;75 ]) then   
                    								add_to_intersected intersected_hash newp intersected_set) filter_p) interferered;																
         end;							 
      *)
			if C.not_in_happy mergepredicate then begin	
                       C.compute_successor mergepredicate;														
                      List.iter (fun r -> let strength_p = R.strengthen r mergepredicate in List.iter (fun newp -> 
												   if example = "Unordered" && ( C.pc newp 0 = 70 || C.pc newp 0 = 50)  then C.set_pc newp 0 18;
												   if (example = "HMset1" && List.mem (C.pc newp 0) [23;22;20]) || 
												   (example = "MMichael" && List.mem (C.pc newp 0) [23;22;20]) || 
													 (example = "THarris" && ((C.pc newp 0 <> 37) )) || 
													 (example = "Unordered" && (List.mem (C.pc newp 0) [18; 12; 31; 30; 43; 80; 60;  50; 70; 80; 56; 58; 79; 77 ])) ||
													 (example <> "THarris" && example <> "MMichael" && example <> "HMset1" && example <> "Unordered") then add_to_intersect intersect_hash newp intersect_set) strength_p) interferers;
                                               
                      List.iter (fun r -> let filter_p = R.filter r mergepredicate in List.iter (fun newp ->   if (example = "Unordered" && (List.mem (C.pc newp 0) [12;2; 13; 18; 22;      43; 47; 50; 54; 44;  86;90 ;  37;39;70;75 ])) || example <> "Unordered" then  add_to_intersected intersected_hash newp intersected_set) filter_p) interferered;																
                    end;																																				
																																																																									 
															(*raise the condidition here to finish the loop*)
															raise (EndLoop 0);
									        end;												
								      end
											else
             begin (*if C.in_queue oldpredicate = false then*) raise (EndLoop 1) end;
											end
											else if (C.compare_constraint predicate oldpredicate) then raise (EndLoop 1);
											
			             done;
									 raise (EndLoop 2)
									with
           | (EndLoop 2) -> ()
           | (EndLoop 0) -> ()
           | (EndLoop 1) -> ()
         end
            end						 							  														 
in
let compute_inference p p1 p2 = begin 
	let fro = (C.gvar p1) -1 in
  let til = C.bound p1 in
  C.pure_strengthen p;
  let pp = C.clone p in
	(*HW queue*)
	for i = 0 to (List.length interferers)-1 do	
			let inter_r = List.nth interferers i in		
			let post_constraintlist = R.post_interf inter_r p in						
      if (List.length post_constraintlist) > 0 then begin																																											
				(*Abstract aways the second thread*)					 
			  for j = 0 to List.length(post_constraintlist) - 1 do						
       let merge_p = (List.nth post_constraintlist j) in	
       
							 let interf_cons = C.abstract_away merge_p fro til p2 in
						  
       if not (C.compare_constraint interf_cons p2) then 
         begin  
           insert_in_system (interf_cons); 
           
         end;  
       if C.test2 p2   then							
        begin 
          C.print_cons interf_cons; 
            end
	      done;		
  end;
 done; 
end in
let intersection s1 s2 i1 i2 j1 j2  = begin		
	for i = i1 to i2 - 1 do
		for j = j1 to j2 - 1 do
			let p1, p2 = s1.(i), s2.(j) in
		if C.interested p1 && C.interested p2 && C.observer p1 = C.observer p2 then begin 
				begin 
			       (*I we need to compute intersection*)  	
      (*it depend on how you start, for DGLM, we may start from T*)		
       
                
						 let sp1,sp2 = if example = "DGLM" then begin C.start_point p1, C.start_point p2; end else 3,3 in
       let org_time = Sys.time () in  
          
      let interConstraintList, res = if sp1 = sp2 then C.do_intersection p1 p2 sp1 sp1 sp1 1 else [],false in
      (*
       let interConstraintList, res =  C.do_full_intersection p1 p2 1  in 
        *)
    
             if res then begin
								(*Compute inference*)	
								List.iter(fun x -> compute_inference x p1 p2) interConstraintList;
					   end
				end
			end
		done;
	done;
end in
let insert_in_system1 (predicate:C.t) = begin  
						let signature = 	C.signature predicate in
						let pc        =   C.pc predicate 0 in	
						let ok = ref 1 in
						
						for i = 0 to Array.length !test -1 do
						   if C.compare_constraint predicate !test.(i) then
								begin ok := 0;  end;
						done;		
						
						if !ok = 1 then begin
									 	test := Array.append !test [|predicate|];
																		C.set_in_queue predicate false; 
											add_to_w predicate;   		
						end;			
end in
 let rec work' _ = begin (* make the call tail-recursive *)    
      let _current = try Some (Q.take w) with Q.Empty -> None in		
      match _current with
      | None -> ()
      | Some current ->
       C.set_in_queue current false;			
       if C.pc current 0 = 15 && C.interested current && C.test3 current  then begin C.print_cons current; end;	
       if C.not_in_happy current then begin	
          List.iter (fun (r:R.t) -> let new_post_current = R.post r current in 
          List.iter insert_in_system1 (new_post_current); ) transformers;
       end;
			work'()
		end in

let dotheabstractjob f = begin 
		let old_intersect_len,old_intersected_len = !intersect_len,!intersected_len in
		intersection intersect_set intersected_set 0 !intersect_len 0 !intersected_len;
		let new_intersect_len,new_intersected_len = !intersect_len,!intersected_len in
		
		let rec dotheabstractloop old_intersect_len old_intersected_len new_intersect_len new_intersected_len = 
			begin
		    intersection intersect_set intersected_set old_intersect_len new_intersect_len 0 new_intersected_len;
        intersection intersect_set intersected_set 0 old_intersect_len old_intersected_len new_intersected_len;
     work ();	

		    let old_intersect_len = new_intersect_len in
		    let new_intersect_len = !intersect_len in
		    let old_intersected_len = new_intersected_len in
		    let new_intersected_len = !intersected_len in
		    if old_intersect_len <> new_intersect_len || old_intersected_len <> new_intersected_len then
        dotheabstractloop old_intersect_len old_intersected_len new_intersect_len new_intersected_len
		end in
		dotheabstractloop old_intersect_len old_intersected_len new_intersect_len new_intersected_len;
end	in	




    let dotheabstractjob' f = begin 
		let old_intersect_len,old_intersected_len = !intersect_len,!intersected_len in
      intersection intersect_set intersected_set 0 !intersect_len 0 !intersected_len;
      let new_intersect_len,new_intersected_len = !intersect_len,!intersected_len in
     
      
      intersection intersect_set intersected_set old_intersect_len (new_intersect_len) 0 new_intersected_len;
      
      
         end	in	
      
  
      let dothejob f = begin
        work ();		   
         
      dotheabstractjob ();
    
 end in
    (* Initialization *)
    List.iter (fun x -> insert_in_system x) (E.initial_predicates);
						let org_time = Sys.time () in  
		 try
			dothejob ();
			
(*///////////////////////////////////////////////////////////////////////////////TEST/////////////////////////////////////////////////////////////////////////////////////////////////////////*)			
(*////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)	

for i = 0 to !intersected_len - 1  do
  if C.pc intersected_set.(i) 0 > 222220 && C.interested intersected_set.(i)  then begin C.print_cons intersected_set.(i); print_int  (C.pc intersected_set.(i) 0); print_string "\n"; end;
done;	
for i = 0 to !intersect_len - 1 do
  if (C.pc intersect_set.(i) 0 = 1822) && C.interested intersect_set.(i) then C.print_cons intersect_set.(i);
done;							
		
		Array.iter (fun x -> if C.interested x then C.print_cons x) !fixed2;
		
	 Debug.print "Time of Process: %.2f s | System: %d \n" ((Sys.time ()) -. org_time) (Hashtbl.length(working_set));
    with
    | C.Dangling (p,reason) ->
	Debug.print "Dangling pointer: ";
	if !Globals.progress then begin
	  Debug.print "" ;	  
	end;
	Debug.print "";
    | C.NullPointerDereferencing (p,reason) ->
	Debug.print "Null pointer dereferencing: ";
	if !Globals.progress then begin
	  Debug.print "";
	end;
	Debug.print "";
    | C.FreeDereferencing (p,reason) ->
	Debug.print "Free cell dereferencing: ";
	if !Globals.progress then begin
	  Debug.print "";
	end;
end
end
*)

