open Printf
let iflist = ref []
let file = "example.txt"
let ofile = "example.ml"
(*let message = Sys.argv.(1)*)
type op = {l:string; o:string; r:string} 
(*
let message = "20: [x  :=        y.next; x = y  ; succ.next := pred  ;  b := a ;  f.data := xyz ; ]:    30 \n  30: [succ = curr; pred.data = 2; pred.data = curr.data; x.data < y.data; pred.next = t; p.data <> c.data; x <> y;] : 40"  
 *)
(*
let message = "20: [x := y.next; y.data < x.data; x := y;] : 40 \n 20: [x := y.next; y.data < x.data; x := y;] : 40"
*)

(*
let message =   "20: [cas (pred, curr, succ)] : 30 "
*)
(*
let message =   "20: [linearize (push, x, true)] : 30 "
*)
(*
let message =   "20: [x := new;] : 30 "
*)
(*let message =   "20: [kill_thread] : 30 "*)

(*let message =   "20: [create_stack (h, t, marked)] : 30 "*)
let message = "global: pred, succ, curr;"

let cut_var var = begin
try 
	let cut = String.index var '.' in
	String.sub var 0 cut
with Not_found -> var	
end

(*let message =   "20: [initial_thread (pred, curr, succ)] : 30 "*)
let get_pc stm = begin
  let i = String.index stm ':' in
  let pc1 = String.sub stm 0 i in
 let ri = String.rindex stm ':' in
  let pc2 = String.sub stm (ri+1) ((String.length stm) - ri-1) in
 ( (String.trim pc1), (String.trim pc2) );
end
  
  
let get_op op = begin
  let left = String.index op ' ' in
  let right = String.rindex op ' ' in
  let lhs = String.sub op 0 left in
  let operation  = String.sub op (left+1) (right-left-1) in  
  let rhs = String.sub op (right) ((String.length op) - right) in
  {l = lhs;  o = operation;r = rhs}
end
  
let contains s1 s2 = begin
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with Exit -> true	
end	


let transfer_initial_thread_line stm = begin
  let pc1,pc2 = get_pc stm in   
   let stm' =  String.trim stm in
   let i1 = String.index stm' '(' in
   let i2 = String.index stm' ')' in
   let vars = String.trim (String.sub stm' (i1+1) (i2-i1-1)) in
let flag = ref true in
   let stm'' = ref vars in
	 let fst_var = ref "" in
	 let count = ref 0 in
	 let ret = ref "" in 
   while !flag; do 
     let cut = try let cut' = String.index !stm'' ',' in cut'  with Not_found -> flag := false; (String.length !stm'') in
     if cut = 0 then flag := false
     else begin
       let var =  String.sub !stm'' 0 cut in
			 count := !count + 1;
	   
			  if !stm'' = vars then fst_var := var;
				ret := String.concat " " [!ret; if !ret <> "" then ";" else ""; cut_var var];			 
			  if !flag then stm'' := String.trim (String.sub !stm'' (cut+1) (String.length !stm'' - cut -1)); 
     end; 
   done;
	ret:= String.concat " " ["(new R.initial_thread "; pc1; pc2; "[|";!ret;"|]"; ");"];
  !ret
end  

let transfer_kill_thread_line stm = begin
  let pc1,pc2 = get_pc stm in   
	let ret = ref "" in
	ret:= String.concat " " ["(new R.kill_thread "; pc1; pc2; ")"];
 !ret
  
end  

let transfer_dec_variable_line stm = begin
	let cut = String.index stm ':' in
	let variable_type = String.sub stm 0 cut in
	let cut2 = String.index stm ';' in
	let vars = String.sub stm (cut+1) (cut2 - cut - 1) in  
	         (* flush and close the channel *)
	let flag = ref true in
   let stm'' = ref vars in
	 let count = ref 0 in
	 let ret = ref "" in 
   while !flag; do 
     let cut = try let cut' = String.index !stm'' ',' in cut'  with Not_found -> flag := false; (String.length !stm'') in
     if cut = 0 then flag := false
     else begin
       let var =  String.sub !stm'' 0 (cut) in print_string var;
			 count := !count + 1;
	     let transfered_var = String.concat "" ["let "; var; "= Label."; variable_type; "("; if variable_type = "global" then string_of_int (!count+2) else string_of_int (!count-1) ; ","; var; ")"] in
			 ret := String.concat " " [!ret;transfered_var;"\n"];		 
			  if !flag then stm'' := String.trim (String.sub !stm'' (cut+1) (String.length !stm'' - cut -1)); 
     end; 
   done;
	!ret
end



let transfer_cas_line stm pc1 pc2 = begin 
   let stm' =  String.trim stm in
   let i1 = String.index stm' '(' in
   let i2 = String.index stm' ')' in
   let vars = String.trim (String.sub stm' (i1+1) (i2-i1-1)) in
   let flag = ref true in
   let stm'' = ref vars in
	 let fst_var = ref "" in
	 let count = ref 0 in
	 let ret = ref "" in 
   while !flag; do 
     let cut = try let cut' = String.index !stm'' ',' in cut'  with Not_found -> flag := false; (String.length !stm'') in
     if cut = 0 then flag := false
     else begin print_string !stm''; print_string "\n"; print_int cut;
       let var =  String.sub !stm'' 0 cut in
			 count := !count + 1;
	   
			  if !stm'' = vars then fst_var := var;
				ret := String.concat " " [!ret; cut_var var];			 
			  if !flag then stm'' := String.trim (String.sub !stm'' (cut+1) (String.length !stm'' - cut -1)); 
     end; 
   done;
    if !count = 4 then ret:= String.concat "" ["(new R.cas_"; if contains stm "success" then "success" else "fail"; "_set ";!ret; ")"]  
				else
				if contains !fst_var ".next" then ret:= String.concat "" ["(new R.cas_next_";if contains stm "success" then "success" else "fail";!ret; ")"]  
				else 			  
					  if contains !fst_var ".data" then ret:= String.concat "" ["(new R.cas_data_";if contains stm "success" then "success " else "fail "; !ret; ")"]  
					  else
				 		  ret:= String.concat "" ["(new R.cas_";if contains stm "success" then "success " else "fail ";  pc1; " "; pc2; " " ; !ret; ")"];
	!ret
end


let transfer_create_stack_line vars = begin
let flag = ref true in
   let stm'' = ref vars in
	 let fst_var = ref "" in
	 let count = ref 0 in
	 let ret = ref "" in 
   while !flag; do 
     let cut = try let cut' = String.index !stm'' ',' in cut'  with Not_found -> flag := false; (String.length !stm'') in
     if cut = 0 then flag := false
     else begin
       let var =  String.sub !stm'' 0 cut in
			 count := !count + 1;
	   
			  if !stm'' = vars then fst_var := var;
				ret := String.concat " " [!ret; cut_var var];			 
			  if !flag then stm'' := String.trim (String.sub !stm'' (cut+1) (String.length !stm'' - cut -1)); 
     end; 
   done;
   ret:= String.concat " " [!ret;];
	!ret
end

let transfer_linearize_line stm pc1 pc2 = begin  
   let stm' =  String.trim stm in
   let i1 = String.index stm' '(' in
   let i2 = String.index stm' ')' in
   let vars = String.trim (String.sub stm' (i1+1) (i2-i1-1)) in
let flag = ref true in
   let stm'' = ref vars in
	 let fst_var = ref "" in
	 let count = ref 0 in
	 let ret = ref "" in 
   while !flag; do 
     let cut = try let cut' = String.index !stm'' ',' in cut'  with Not_found -> flag := false; (String.length !stm'') in
     if cut = 0 then flag := false
     else begin
       let var =  String.sub !stm'' 0 cut in
			 count := !count + 1;
	   
			  if !stm'' = vars then fst_var := var;
				if !stm'' <> vars then ret := String.concat " " [!ret; cut_var var];			 
			  if !flag then stm'' := String.trim (String.sub !stm'' (cut+1) (String.length !stm'' - cut -1)); 
     end; 
   done;
	ret:= String.concat "" ["(new R.validate_"; String.trim !fst_var; " "; pc1; " "; pc2; " "; !ret; ")"];
	!ret
end

let transfer_op op pc1 pc2  = begin 
  let newop = get_op (String.trim op) in 
  let l,o,r = newop.l,newop.o,newop.r in
	let defined_stm_1 = "(new R." in
	let defined_stm_2 = ");" in
	let operation = ref " " in
	let ret = ref "" in 
	begin
  match String.trim o with
    | ":=" -> (*check if l or right is data, pointer or variable only*)
				 let newl, newr = ref l,ref r in
		     if contains l ".next" then begin operation :=  "dot_next_assign"; newl := String.sub l 0 (String.index l '.') end else
										  if contains l ".data" then begin operation :=  "data_assign"; newl := String.sub l 0 (String.index l '.') end else
										  if contains r ".next" then begin operation := "assign_dot_next"; newr := String.sub r 0 (String.index r '.') end else
										  if contains r ".data" then operation := "not_suport" else
												if contains r "new" then operation := "new_cell" else operation:="equality";	
										
											 if contains r "new" then ret := String.concat "" [defined_stm_1; !operation; " "; pc1; " "; pc2; " "; !newl; " "; defined_stm_2]
					else ret := String.concat "" [defined_stm_1; !operation; " "; pc1; " "; pc2; " "; !newl; " "; !newr; " "; defined_stm_2];  
		   
		 | "=" -> (*check if l or right is data, pointer or variable only*)
				 let newl, newr = ref l,ref r in
		     if contains l ".next" then begin operation :=  "dot_next_equalilty"; newl := String.sub l 0 (String.index l '.') end else
										  if contains l ".data" then if contains r ".data" = false then begin operation :=  "data_equality"; newl := String.sub l 0 (String.index l '.') end else begin operation :=  "data_equality_variable"; newl := String.sub l 0 (String.index l '.');newr := String.sub r 0 (String.index r '.') end else
										  if contains r ".next" then begin operation := "equality_dot_next"; newr := String.sub r 0 (String.index r '.') end else
										  if contains r ".data" then operation := "not_suport" else
										    operation:="assign";	
		    ret := String.concat "" [defined_stm_1; !operation; " "; pc1; " "; pc2; " "; !newl; " "; !newr; " "; defined_stm_2];  
		| "<" -> (*check if l or right is data, pointer or variable only*)
				 let newl, newr = ref l,ref r in
										  if contains l ".data" && contains r ".data" then begin operation :=  "less_than"; newl := String.sub l 0 (String.index l '.');newr := String.sub r 0 (String.index r '.') end  else
										 operation:="not_support";	
		      ret := String.concat "" [defined_stm_1; !operation; " "; pc1; " "; pc2; " "; !newl; " "; !newr; " "; defined_stm_2];  
		| "<>" -> (*check if l or right is data, pointer or variable only*)
				 let newl, newr = ref l,ref r in
		     if contains l ".next" then begin operation :=  "dot_next_inequalilty"; newl := String.sub l 0 (String.index l '.') end else
										  if contains l ".data" then if contains r ".data" = false then begin operation :=  "data_inequality"; newl := String.sub l 0 (String.index l '.') end else begin operation :=  "data_inequality_variable"; newl := String.sub l 0 (String.index l '.');newr := String.sub r 0 (String.index r '.') end else
										  if contains r ".next" then begin operation := "inequality_dot_next"; newr := String.sub r 0 (String.index r '.') end else
										  if contains r ".data" then operation := "not_suport" else
										 operation:="inequality";	
		     ret := String.concat "" [defined_stm_1; !operation; " "; pc1; " "; pc2; " "; !newl; " "; !newr; " "; defined_stm_2];   
		
    | _ -> operation := " ";
   end;
	!ret
end  
  

let transfer_ops ops pc1 pc2  = begin 
	let transfered_ops = ref "" in 
	for i = 0 to List.length ops - 1 do
	   let op = List.nth ops i in
		 let oppc1 = if i = 0 then pc1 else String.concat "" ["(-"; (string_of_int i); ")"] in
		 let oppc2 = if (i) = (List.length ops - 1) then pc2 else String.concat "" ["(-"; string_of_int (i+1); ")"] in
		 let transfered_op = transfer_op op oppc1 oppc2 in
		  transfered_ops := String.concat "" [!transfered_ops; transfered_op];
	done;
	!transfered_ops
end  


let get_ops stm pc1 pc2 = begin
   let stm' =  String.trim stm in
   let i1 = String.index stm' '[' in
   let i2 = String.index stm' ']' in
   let ops = String.trim (String.sub stm' (i1+1) (i2-i1-1)) in
   let ret = ref [] in
   let flag = ref true in
   let stm'' = ref ops in
    while !flag; do 
     try
     let cut = String.index !stm'' ';' in
     if cut = 0 then flag := false
     else begin
       let op =  String.sub !stm'' 0 cut in
       ret := !ret @ [op];
       stm'' := String.trim (String.sub !stm'' (cut+1) (String.length !stm'' - cut -1)); 
     end
     with Not_found -> flag := false;
   done;
	let full_transfered_ops = String.concat "" ["(new R.atomic"; " "; pc1; " "; pc2; " [ ";  transfer_ops !ret pc1 pc2; " ]);"]    in
	full_transfered_ops;

end   

let transfer_op1  op oppc1 oppc2 = begin
if contains op "cas" then transfer_cas_line op oppc1 oppc2
else
if contains op "linearize" then transfer_linearize_line op oppc1 oppc2
else
	""
end


let transfer_ops1 ops pc1 pc2  = begin 
	let transfered_ops1 = ref "" in 
	for i = 0 to List.length ops - 1 do
	   let op = List.nth ops i in
		 let oppc1 = if i = 0 then pc1 else String.concat "" ["(-"; (string_of_int i); ")"] in
		 let oppc2 = if (i) = (List.length ops - 1) then pc2 else String.concat "" ["(-"; string_of_int (i+1); ")"] in
		 let transfered_op1 = transfer_op1 op oppc1 oppc2 in
		  transfered_ops1 := String.concat "" [!transfered_ops1;if !transfered_ops1 <> "" then ";" else ""; transfered_op1];
	done;
	!transfered_ops1
end  



let get_ops1 stm pc1 pc2 = begin
   let stm' =  String.trim stm in
   let i1 = String.index stm' '[' in
   let i2 = String.index stm' ']' in
   let ops = String.trim (String.sub stm' (i1+1) (i2-i1-1)) in
   let ret = ref [] in
   let flag = ref true in
   let stm'' = ref ops in
    while !flag; do 
     try
     let cut = String.index !stm'' ';' in
     if cut = 0 then flag := false
     else begin
       let op =  String.sub !stm'' 0 cut in
       ret := !ret @ [op];
       stm'' := String.trim (String.sub !stm'' (cut+1) (String.length !stm'' - cut -1)); 
     end
     with Not_found -> flag := false;
   done;
	let full_transfered_ops1 = String.concat "" ["(new R.atomic"; " "; pc1; " "; pc2; " [ ";  transfer_ops1 !ret pc1 pc2; " ]);"]    in
	full_transfered_ops1;

end   

			let transfer_line1 line = begin		
		     let pc1, pc2 = get_pc line in
      get_ops1 line pc1 pc2;
end				
							    
let transfer_line line = begin		
		     let pc1, pc2 = get_pc line in
      get_ops line pc1 pc2;
end			




let transfer_statement_from_file stm = begin
if contains stm "create" then
	transfer_create_stack_line stm 
else
if contains stm "local" || contains stm "global" then
	transfer_dec_variable_line stm
else
if contains stm "initial_thread" then
	transfer_initial_thread_line stm 
else
if contains stm "kill" then
	transfer_kill_thread_line stm 
else
if contains stm "cas" then
	transfer_line1 stm 
else
if contains stm "linearize" then
	transfer_line1 stm
else
	transfer_line stm
end


let () =
  (* Read file and display the first line *)
		let output = ref 
		"module C = Constraint \n
  	 module R = Rule   \n 
		 module Reset : Example.E = struct \n
		  let null = Label.nil \n
  let free = Label.free \n " 
		in
	let mm = ref "" in
	  let ic = open_in file in
  try 
    let count = ref 1 in
    while true; do
      let line = input_line ic in  (* read line from in_channel and discard \n *)
		    if line <> "" then begin if contains (transfer_statement_from_file line) "create_" then output := String.concat "" [!output;" let initial_predicates  = \n";(transfer_statement_from_file line);"\n"; "let predicate_transformers = \n [ \n"] else output := String.concat "" [!output;(transfer_statement_from_file line);"\n"]; end;
					
					(* (print_endline (string_of_int !count));          (* write the result to stdout *)*)
          iflist := !count :: !iflist; 
       
    flush stdout;                (* write on the underlying device now *)
      count := !count +1;
    done;
						 
  with End_of_file -> output := String.concat "" [!output; "] \n end"];
  close_in ic;                     

	let oc = open_out ofile in    (* create or truncate file, return channel *)
	let message = ref "x' y'" in
	print_string !output;
  fprintf oc "%s \n" (!output);   (* write something *)   
  close_out oc;                (* flush and close the channel *)

	(* exit with error: files are closed but
                                    channels are not flushed *)
      
      
     
  (* normal exit: all channels are flushed and closed *)