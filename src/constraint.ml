(*data_assign is differenct for hidsign and other sets*)
(*assign_dot_next is different for stack,queue and set*)
(*strengthen attemp mark is different for harris and other set*)
(*observer is s2 for harris, michael but its init for hidsign and lockfree*)
let sprintf = Printf.sprintf
exception BreakLoop of int
let example_name = ref ""
let property_name = ref ""
let debug = false
let debugJOIN = false
let final_result = ref "VALID"
let debugJOIN_Info = false
let debugPermute = false
let debugEXTEND = false
let inter_time = ref 0.00000
(* Global counter, for identification *)  
let maxID = ref (-1)
type ex = Q | Rest
let b = Buffer.create 20000 (* Buffer for the to_dot printing *)
let key = Buffer.create 1000000
type lockstate = Me | Others | Unlocked
let string_of_lockstate = function | Me -> "Me" | Others -> "Others" | Unlocked -> "Unlocked"
type datafield = Marked | Notmarked | Locked_by_Me | Locked_by_Other | Notlocked
let char_of_lockstate = function | Me -> '*' | Others -> 'o' | Unlocked -> 'u'
type data = {d1:int; d2:int;d3:int*int}
type cut = {r1: Info.t; d:data ;}
type obs = Init | T | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S1' | S2' | Bad | Happy
type flag = Interf | Alone | Un_cnt_rem | Cnt_un_add
type help = {pc:int list; op: int; ret: bool; ord :int}
type ret = {cnt:int; add:int; rmv:int}
let alone_ret = {cnt = 16; add = 16; rmv = 16}
(* ========================================================================== *)
type thread = {
    mutable pc: int;
		mutable interf_pc: int;
    mutable return: Data.t;
    mutable trans: string array;
    mutable lbound: int;
    mutable range: int;
  }
      
let thread_create  lbound = begin
  { 
    pc=0;
	interf_pc = 0;
    return=Data.top;
    trans=[||];
   lbound=lbound; 
   range=0;
  } 
end
let thread_clone th = {th with lbound= th.lbound;}
 
(* ========================================================================== *)

type t = {    
    mutable observer: obs;      (** The state of the observer *)
    mutable start_observer: obs;      (** The state of the observer *)  
	mutable start_events: int array;      (** The state of the observer *)    			    
	mutable events: int array;      (** The state of the observer *)      		
    mutable nth:int;
    mutable threads: thread array;
    mutable heap: Info.t array array;
	mutable scope: int array;
	mutable data: data array;
	mutable cut:  cut array;
    mutable bound: int;
	mutable successor: (int,int) Hashtbl.t; 
    gvar: int;
    gvars: Label.t array;
	mutable value_vars: int array; (*value of variables*)
	mutable bool_vars: Label.t array;
    mutable vars: Label.t array;
    mutable translation: string array;    
    mutable in_queue: bool;
    mutable interested: bool;
	mutable flag: flag;
	mutable ret: ret;
	mutable interf_ret: ret;
	mutable interf_flag: flag;
    mutable helper: bool;
	mutable x_red: bool;
    id:int;
    example:ex;
  } 
let emp_constraint = {
  example=Rest;
  observer = Init;
	flag = Alone;
	interf_flag = Alone;
  ret = alone_ret;
	interf_ret = alone_ret;
	start_observer = Init;
	start_events = [||];
	events = [||];
  nth = 0;
  threads = [||];
  heap = Array.make_matrix 1 1 Info.none;
	scope = [||];
	data = [||];
	cut = [||];
  gvar = 0;
  bound = 1;
	successor = Hashtbl.create 1;
	vars = [||];
                      gvars = [||];
                      value_vars = [||];
	bool_vars = [||];
  translation = [||]; 
  in_queue=false;  
  interested = false;
  helper = false;
	x_red = true;
  id = 0;
}

let create ?(example=Rest) nth gvars bvars  = incr maxID;
  let gvar = 3 + Array.length gvars in (* 3 = null, bottom and free *)
  let bound = gvar - 1 in
  let bound' = bound+1 in
  let h = Array.make_matrix bound' bound' Info.none in
	let s = Array.make bound' 15 in	
	let d = Array.make bound' {d1 = 1;d2 = 1;d3 = (0,4);} in
	let c = Array.make bound' {r1 = Info.none; d = {d1 = 15; d2 = 15; d3 = (0,4)};} in
	let succ = Hashtbl.create bound' in
  for i=0 to bound do for j=0 to bound do h.(i).(j) <- (if i=j then Info.equal else Info.none); done; done;
  let threads = Array.init nth (fun _ -> thread_create  (gvar)) in
  {
  example=example;
  observer = Init;
  start_observer = Init;
	flag = Alone;
	x_red = true;
	interf_flag = Alone;
	ret = alone_ret;
	interf_ret = alone_ret;
	start_events = [||];
  events = [||];
  nth = nth;
  threads = threads;
  heap = h;
	scope = s;
	data = d;
	cut = c;
   gvar = gvar;
   gvars = gvars;
  bound = bound;
	successor = succ;
	vars = [||];
	value_vars = [||];
	bool_vars = bvars;
  translation = Array.append
  (Array.map Label.string_of (Array.append [|Label.nil;Label.bottom;Label.free(* ;Label.locked *)|] gvars))
     (Array.map Data.string_of [||]); 
  in_queue=false;  
  interested = true;
  helper = false;
  id = (!maxID);
}
let create_s ?(example=Rest) nth gvars    = incr maxID;
  let gvar = 3 + Array.length gvars in (* 3 = null, bottom and free *)
  let g = gvars in
 let bound = gvar - 1 in
  let bound' = bound+1 in
  let h = Array.make_matrix bound' bound' Info.none in
	let s = Array.make bound' 15 in
	let d = Array.make bound' {d1 = 1;d2 = 1;d3 = (0,4)} in
	let c = Array.make bound' {r1 = Info.none; d = {d1 = 15; d2 = 15; d3 = (0,4)}} in
	let succ = Hashtbl.create bound' in
  for i=0 to bound do for j=0 to bound do h.(i).(j) <- (if i=j then Info.equal else Info.none); done; done;
  let threads = Array.init nth (fun _ -> thread_create (gvar)) in
  {
  example=example;
  observer = Init;
  start_observer = Init;
	flag = Alone;
	interf_flag = Alone;
	x_red = true;
	ret = alone_ret;
	interf_ret = alone_ret;
	start_events = [||];
	events = [||];
  nth = nth;
  threads = threads;
  heap = h;
	scope = s;
	data = d;
	cut = c;
   gvar = gvar;
   gvars = gvars;
  bound = bound;
	successor = succ;
	vars = [||];
	value_vars = [||];
	bool_vars = [||];
  translation = Array.append
  (Array.map Label.string_of (Array.append [|Label.nil;Label.bottom;Label.free(* ;Label.locked *)|] gvars))
     (Array.map Data.string_of [||]); 
  in_queue=false;  
  interested = true;
  helper = false;
  id = (!maxID);
}

let _clone t id =
  { t with id=id;
    threads = Array.map thread_clone t.threads;
    heap = Array.map Array.copy t.heap;
		scope = Array.copy t.scope;
		data =  Array.copy t.data;
		cut = Array.copy t.cut;
    value_vars = Array.copy t.value_vars;
     gvars = Array.copy t.gvars;
    ret = t.ret;
    interf_ret = t.interf_ret;
    translation = Array.copy t.translation;
  }

let clone t = incr maxID; _clone t (!maxID)
(* ========================================================================================================= *)
(* =====================                        Utilities                           ======================== *)
(* ========================================================================================================= *)
let is_q p = match p.example with Q -> true | _ -> false (* p.gvar > 4 *)
let set_example_name example = example_name := example
let set_property_name example = property_name := example
let id t = t.id
let observer t = t.observer
let set_observer t obs = t.observer <- obs
let not_in_happy t = t.observer <> Happy &&  (t.observer <> Bad)   
let not_in_s2 t = (t.observer == S2)     
let nthreads p = p.nth
let gvar p = p.gvar
let var p = Array.length p.vars
let set_in_queue t v = t.in_queue <- v
let set_interested t v = t.interested <- v
let set_helper t v = t.helper <- v
let in_queue t = t.in_queue
let interested t = t.interested
let helper t = t.helper
let pc p thi = p.threads.(thi).pc
let bound p = p.bound
let interf_pc p thi = p.threads.(thi).interf_pc
let set_pc p thi pc = p.threads.(thi).pc <- pc  
let set_return p thi d = p.threads.(thi).return <- d
(* =================================================================================== *)
let index p thi v = begin (* thi is a physical index *)
  if Label.is_global v
  then Label.unpack v
  else begin
    let shift = Label.unpack v in
    let th = p.threads.(thi) in
    th.lbound + shift
  end
end
exception NullPointerDereferencing of t * (string Lazy.t)
exception DoubleFree of t * (string Lazy.t)
exception Dangling of t * (string Lazy.t)
exception FreeDereferencing of t * (string Lazy.t)
exception Cycle of t * (string Lazy.t)
exception IgnoreConstraint
exception ClashWithInit of t
exception EndLoopWithResult of int
exception EndLoopWithNothing of int
exception Compare of int
let empty_attribute = {r1 = Info.none; d = {d1 = 15; d2 = 15; d3 = (0,4)};} 
let local_attribute =  {r1 = Info.reach1; d = {d1 = 2; d2 = 1; d3 = (0,4)};} 
	
let local_unordered_attribute = {r1 = Info.reach_unordered; d = {d1 = 16; d2 = 1; d3 = (0,4)};} 
		
let string_of_state s = match s with
| Init -> "init"
| S1 -> "S1"
| S2 -> "S2"
| S3 -> "S3"
| S4 -> "S4"
| S5 -> "S5"
| S6 -> "S6"
| S7 -> "S7"
| S1' -> "S1'"
| S2' -> "S2'"
| T -> "Temp"
| Bad -> "Bad"
| Happy -> "Happy"

let string_of_flag s = match s with
| Alone -> "Alone"
| Interf -> "Interf"
| Un_cnt_rem -> "Un_cnt_rem"
| Cnt_un_add -> "Cnt_un_add"  



let print_cons p = begin
  print_string "\n\n";
  print_string "PC: "; print_int p.threads.(0).pc; print_string "\n"; 
	print_string "XRED: "; if p.x_red then  print_string "true" else print_string "false"; print_string "\n"; 
	print_string "Flag: "; print_string (string_of_flag p.flag); print_string "\n"; 
  print_string "Return: "; print_string "( "; print_string "cnt = "; print_int p.ret.cnt; print_string ", add = "; print_int p.ret.add; print_string ", rmv = "; print_int p.ret.rmv; print_string " )"; print_string "\n";
	print_string "Start Events: "; Array.iter (fun i -> print_int i) p.start_events; print_string "\n";
  print_string " Events: "; Array.iter (fun i -> print_int i) p.events; print_string "\n";
	print_string "Start Observer State: "; print_string (string_of_state p.start_observer); print_string "\n";
	print_string "Observer State: "; print_string (string_of_state p.observer); print_string "\n";
	print_string "=============================================================================================================================================================================\n";
	print_string "         ";
	for i=0 to p.gvar - 1 do 
	  print_string (p.translation.(i));
		print_string "         ";
	done;
	for i=0 to (Array.length p.vars) - 1 do 
	  print_string (Label.string_of p.vars.(i)); print_string "         ";
	 done;	
	print_string "\n";
	print_string "----------------------------------------------------------------Scope--------------------------------------------------------------------------------------------------------\n";
	print_string "         ";
	for r=0 to  p.bound do 
	  print_int p.scope.(r);print_string "         ";
	done;
	print_string "\n";
	print_string "----------------------------------------------------------------Marked, Color------------------------------------------------------------------------------------------------\n";
	print_string "         ";
	for r=0 to  p.bound do 
		if r < p.gvar then assert(Debug.print "%s %s %s" Debug.yellow  (p.translation.(r)) Debug.noColor;true)
		else
		assert(Debug.print "%s %s %s" Debug.yellow  (Label.string_of p.vars.(r-p.gvar)) Debug.noColor;true);	
		
	  print_string (if p.data.(r).d1 = 1 then "No" else if  p.data.(r).d1 = 2 then "Yes" else if p.data.(r).d1 = 3 then  "YN" else  string_of_int(p.data.(r).d1));
		print_string ","; print_string 
    (if p.data.(r).d2 = 1 then "W" else if p.data.(r).d2 = 2 then "R" else if p.data.(r).d2 = 4 then "B" else if p.data.(r).d2 = 32 then "Rm"  else "E");
   print_string ","; print_string (if fst p.data.(r).d3 = 1 then "M" else if fst p.data.(r).d3 = 2 then "O" else if fst p.data.(r).d3 = 3 then "MO" else if fst p.data.(r).d3 = 4 then "U" else if fst p.data.(r).d3 = 5 then "MU" else if fst p.data.(r).d3 = 6 then "OU" else if fst p.data.(r).d3 = 7 then "MOU" else string_of_int(snd p.data.(r).d3));
		print_string "_";
   print_string ""; print_string (if snd p.data.(r).d3 = 1 then "M" else if snd p.data.(r).d3 = 2 then "O" else if snd p.data.(r).d3 = 3 then "MO" else if snd p.data.(r).d3 = 4 then "U" else if snd p.data.(r).d3 = 5 then "MU" else if snd p.data.(r).d3 = 6 then "OU" else if snd p.data.(r).d3 = 7 then "MOU" else string_of_int(snd p.data.(r).d3));
		print_string "         ";
	done;	
	print_string "\n";
	print_string "\n-------------------------------------------------------------Variables-------------------------------------------------------------------------------------------------------\n";
	for i=0 to Array.length(p.bool_vars)-1 do 
	     print_string (Label.string_of (p.bool_vars.(i))); print_string ": ";
			 print_int p.value_vars.(i); print_string "              ";
	done;
	print_string "\n-------------------------------------------------------------Cut-Attribute---------------------------------------------------------------------------------------------------\n";
	for i=0 to p.bound do
		   if p.cut.(i) <> empty_attribute then begin 
			 if i < p.gvar then assert(Debug.print "%s %s %s" Debug.yellow  (p.translation.(i)) Debug.noColor;true)
			 else
				assert(Debug.print "%s %s %s" Debug.yellow  (Label.string_of p.vars.(i-p.gvar)) Debug.noColor;true);
			 print_string ": r1 = ";
				Info.print_cell p.cut.(i).r1; print_string "  ;  ";
			 print_string " d = "; 
			 print_string (if p.cut.(i).d.d1 = 1 then "No" else if  p.cut.(i).d.d1 = 2 then "Yes" else if p.cut.(i).d.d1 = 3 then  "YN" else if p.cut.(i).d.d1 = 16 then "INV" else string_of_int(p.cut.(i).d.d1)); print_string ",";
       print_string (if p.cut.(i).d.d2 = 1 then "W" else if p.cut.(i).d.d2 = 2 then "R" else if p.cut.(i).d.d2 = 32 then "Rm" else string_of_int(p.cut.(i).d.d2));
		   print_string ","; print_string (if snd p.cut.(i).d.d3 = 1 then "M" else if snd p.cut.(i).d.d3 = 2 then "O" else if snd p.cut.(i).d.d3 = 3 then "MO" else if snd p.cut.(i).d.d3 = 4 then "U" else if snd p.cut.(i).d.d3 = 5 then "MU" else if snd p.cut.(i).d.d3 = 6 then "OU" else if snd p.cut.(i).d.d3 = 7 then "MOU" else "E");			 
			  print_string "\n";
			 end;
	done;
    print_string "\n---------------------------------------------------------------------------------Info----------------------------------------------------------------------------------------\n";

	  for i = 0 to p.bound do
			if i < p.gvar then begin  print_string (p.translation.(i));print_string "        " end
			else
			begin print_string (Label.string_of p.vars.(i- p.gvar)); print_string "        " end;
			
		for j=0 to p.bound do			  
			if (not (Info.is_none_no_ord p.heap.(i).(j))) && j < p.gvar then begin assert(Debug.print "%s %s %s" Debug.yellow  (p.translation.(j)) Debug.noColor;true);Info.print_cell p.heap.(i).(j);print_string "        "; end
			else
				 if (not (Info.is_none_no_ord p.heap.(i).(j))) && j >= p.gvar then begin
					assert(Debug.print "%s %s %s" Debug.red  (Label.string_of p.vars.(j-p.gvar)) Debug.noColor;true);Info.print_cell p.heap.(i).(j);print_string "        ";
			  end
			  else
					begin
				Info.print_cell p.heap.(i).(j);print_string "        ";
				end;
		done;
	print_string "\n----------------------------------------------------------------------------------------------------------------------------------------------------------------------------\n";
		done;


	print_string "\n\n";
  let  rec print v1 = begin
		let time = ref 0 in
		let next_var = ref 0 in
		if v1 < p.gvar then  assert(Debug.print "%s %s %s" Debug.yellow  (p.translation.(v1) ^ ":" ^ string_of_int(v1)) Debug.noColor;true)
			     else
				   if v1 >= p.gvar then begin
             assert(Debug.print "%s %s %s" Debug.yellow  (Label.string_of p.vars.(v1-p.gvar)  ^ ":" ^ string_of_int(v1)) Debug.noColor;true) 
					 end;
					
		if v1 == 3 then begin
		for i = 0 to  p.bound do
			if Info.is_equal p.heap.(v1).(i) && i <> v1  && v1 == 3 then begin
									print_string ",";
				if i < p.gvar then  assert(Debug.print "%s %s %s" Debug.yellow  ((p.translation.(i)) ^ ":" ^ string_of_int(i)) Debug.noColor;true)
			     else
				   if i >= p.gvar then  
						  assert(Debug.print "%s %s %s" Debug.yellow  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true)
			     end;
		done;	
		end;	
				for i = 0 to  p.bound do
			if Info.is_reach p.heap.(v1).(i) && !time == 0 then
				begin
					print_string "  "; Info.print_cell p.heap.(v1).(i); print_string "   ";
					time := 1;
					next_var := i;
				end
			else
				if Info.is_reach p.heap.(v1).(i)  then begin
					if i < p.gvar then  assert(Debug.print "%s %s %s" Debug.yellow  ((p.translation.(i)) ^ ":" ^ string_of_int(i)) Debug.noColor;true)
			     else
				   if i >= p.gvar then 
						 assert(Debug.print "%s %s %s" Debug.yellow  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true);
					print_string ",";
				end;				
		done;	
		if !next_var <> 0 then print !next_var;
		end
    in	
 print 3;
				print_string "\n\n";
				print 4;
				print_string "\n\n\n\n\n\n";
end


let print_merge_cons p p1 p2 = begin
	print_string "\n\n";
  print_string "PC: "; print_int p.threads.(0).pc; print_string "\n";
   print_string "Return: "; print_string "( "; print_string "cnt = "; print_int p.ret.cnt; print_string ", add = "; print_int p.ret.add; print_string ", rmv = "; print_int p.ret.rmv; print_string " )"; print_string "\n";
	 print_string "interf Return: "; print_string "( "; print_string "cnt = "; print_int p.interf_ret.cnt; print_string ", add = "; print_int p.interf_ret.add; print_string ", rmv = "; print_int p.interf_ret.rmv; print_string " )"; print_string "\n";
	
  	print_string "Observer State: "; print_string (string_of_state p.observer); print_string "\n";
	print_string "===================================MERGE==========================================\n";
	print_string "       ";
	 for i=0 to p1.gvar - 1 do 
	  print_string (p.translation.(i));
		print_string "      ";
	 done;
	for i=0 to (Array.length p1.vars) - 1 do 
	  print_string (Label.string_of p1.vars.(i)); print_string "      ";
	 done;
	

	
		for i=0 to (Array.length p2.vars) - 1 do 
	  print_string (Label.string_of p2.vars.(i)); print_string "      ";
	 done;
	
		
	print_string "\n";
	print_string "--------------------------------Scope----------------------------------------\n";
				print_string "       ";
		for r=0 to  p.bound do 
	  print_int  p.scope.(r);print_string "      ";
	 done;
	print_string "\n";
	print_string "--------------------------------DATA----------------------------------------\n";
	print_string "       ";
	for r=0 to  p.bound do 
	  print_int  (p.data.(r).d1); print_string ","; print_int  (p.data.(r).d2); print_string "         ";
	done;	
	print_string "\n";
	(*print_string "----------------------------------------------------------------Cutpoint------------------------------------------------------------------\n";
	print_string "         ";
	for r=0 to  p.bound do
		let x,y,z = p.cut.(r) in 
	  Info.print_cell x; print_string ","; print_string (Info.string_of_data (List.nth y 0)); print_string ",";print_string (Info.string_of_data (List.nth y 1)); print_string ","; Info.print_cell z; print_string "         ";
	done;	
	*)
			print_string "\n-------------------------------------------------------------Variables-----------------------------------------------------------------------\n";
	for i=0 to Array.length(p.bool_vars)-1 do 
	     print_string (Label.string_of (p.bool_vars.(i))); print_string ": ";
			 print_int p.value_vars.(i); print_string "              ";
	done;
		print_string "\n-------------------------------------------------------------Cut-Attribute-------------------------------------------------------------------\n";
	for i=0 to p.bound do
		   if p.cut.(i) <> empty_attribute then begin 
			 if i < p.gvar then begin print_int i; assert(Debug.print "%s %s %s" Debug.yellow  (p.translation.(i)) Debug.noColor;true) end
			 else
				begin
				print_int i; assert(Debug.print "%s %s %s" Debug.yellow  (Label.string_of p.vars.(i-p.gvar)) Debug.noColor;true); end;
			 print_string ": r1 = ";
				Info.print_cell p.cut.(i).r1; print_string ";";
			 print_string " d = "; print_int (p.cut.(i).d.d1); print_string ",";print_int (p.cut.(i).d.d2);print_string "\n";
			 end;
	done;
	print_string "\n------------------------------Info-------------------------------------------\n";
	
	  for i = 0 to p1.bound do
			if i < p1.gvar then begin  print_string (p1.translation.(i));print_string "      " end
			else
			begin print_string (Label.string_of p1.vars.(i- p1.gvar)); print_string "        " end;			
		for j=0 to p.bound do			  
			 Info.print_cell p.heap.(i).(j);
			 print_string "      ";	 
		done;
				print_string "\n---------------------------------------------------------------------------\n";		
		done;
		 for i = p1.bound+1 to p.bound do
       print_string (Label.string_of p1.vars.(i- p1.bound-1)); print_string "        " ;	
	   	for j=0 to p.bound do			  
			   Info.print_cell p.heap.(i).(j);
			   print_string "      ";	 
		  done;
				print_string "\n---------------------------------------------------------------------------\n";		
		done;		
		print_string "\n\n";
  let  rec print v1 = begin
		 
		let time = ref 0 in
		let next_var = ref 0 in
		if v1 < p.gvar then  assert(Debug.print "%s %s %s" Debug.red  (p.translation.(v1) ^ ":" ^ string_of_int(v1)) Debug.noColor;true)
			     else
				   if v1 >= p.gvar then 
						if v1 > p1.bound then  
							  assert(Debug.print "%s %s %s" Debug.green  ((Label.string_of p.vars.(v1-p.gvar)) ^":"^ string_of_int(v1)) Debug.noColor;true)						 
						else
							assert(Debug.print "%s %s %s" Debug.yellow  (Label.string_of p.vars.(v1-p.gvar)  ^ ":" ^ string_of_int(v1)) Debug.noColor;true);
		
		if v1 == 3 then begin
		for i = 0 to  p.bound do
			if Info.is_equal p.heap.(v1).(i) && i <> v1  && v1 == 3 then
				if i < p.gvar then 
					assert(Debug.print "%s %s %s" Debug.yellow  ((p.translation.(i)) ^ ":" ^ string_of_int(i)) Debug.noColor;true)
			     else
				   if i >= p.gvar then  
						if i > p1.bound then 
							  assert(Debug.print "%s %s %s" Debug.green  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true)						 
						else
						    assert(Debug.print "%s %s %s" Debug.yellow  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true);
		done;	
		end;
		
				for i = 0 to  p.bound do
			if Info.is_reach p.heap.(v1).(i) && !time == 0 then
				begin
					print_string "  "; Info.print_cell p.heap.(v1).(i); print_string "   ";
					time := 1;
					next_var := i;
				end
			else
				if Info.is_reach p.heap.(v1).(i) then begin
					if i < p.gvar then  assert(Debug.print "%s %s %s" Debug.red  ((p.translation.(i)) ^ ":" ^ string_of_int(i)) Debug.noColor;true)
			     else
				   if i >= p.gvar then  
						if i > p1.bound then 
								 assert(Debug.print "%s %s %s" Debug.green  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true)
						else
						assert(Debug.print "%s %s %s" Debug.yellow  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true);
					print_string ",";
				end;				
		done;	
		if !next_var <> 0 then print !next_var;
		end
    in
				print 3;
				print_string "\n\n";
				print 5;
end

let start_index p = begin 
  let ret = ref (p.bound+1) in
  for i = 3 to p.gvar-1 do
    let flag = ref true in
    for j = 0 to p.bound do
      if (Info.is_reach p.heap.(j).(i) && p.scope.(j) = 1) || (not (Label.is_main_global p.gvars.(i-3)))  then
        flag := false;
    done;
    if !flag && !ret = (p.bound+1) then begin ret := i; end;
  done;
  !ret
end  
  
let start_elim_index p = begin
  let ret = ref (p.bound+1) in
  for i = 3 to p.gvar-1 do 
    let flag = ref true in
    for j = 0 to p.bound do
      if (Info.is_reach p.heap.(j).(i) && p.scope.(j) = 1) || (not (Label.is_elim_global p.gvars.(i-3)))  then
        flag := false;
    done;
    if !flag && !ret = (p.bound+1) then begin ret := i; end;
  done;
  !ret
end  


let next_vars p k  = begin
  let ret = ref [||] in
  for i = 0 to p.bound do
	   if Info.is_reach p.heap.(k).(i) then
       ret := Array.append [|i|] !ret
  done;		
 !ret
end

    
(*Check if k position is leaf*)
let is_leaf p k = begin
  let ret = ref false in
  for i = 0 to 2 do
	   if Info.is_equal p.heap.(k).(i) || Info.is_equal p.heap.(i).(k) then
		    ret := true;
	done;
  !ret
end 

let _mergeover (p:t) x fro till = begin
	let isolated_second_thread_variable k = begin
	 try
		 for i = 3 to p.bound do
     if (i <= fro || i > till) && Info.is_equal p.heap.(k).(i) && i<>k then raise (EndLoopWithResult 1);
	   done;
	   raise (EndLoopWithNothing 1) ;
	with
	| (EndLoopWithResult 1)  -> false
	| (EndLoopWithNothing 1) -> true
	end in
	if isolated_second_thread_variable x then 
		begin
     for i=0 to p.bound do
		  for j=0 to p.bound do
			  if Info.is_reach p.heap.(i).(x) && Info.is_reach p.heap.(x).(j) then 
					 let d1,d2,d3 = p.data.(x).d1, p.data.(x).d2, p.data.(x).d3 in
					 p.heap.(i).(j) <- Info.compose_two_cells p.heap.(i).(x) p.heap.(x).(j) d1 d2 d3;	   
	    done;
	   done;		
	 end
end


     
let prev p k = begin
	let ret = ref (p.bound+1) in
  try
  for i = 0 to p.bound do
	  if Info.is_reach p.heap.(i).(k) then
			begin
       ret := i;
			 raise (EndLoopWithResult 3);
			end; 
  done;
	raise (EndLoopWithNothing 3);
	with
	| (EndLoopWithResult  3) -> !ret
	| (EndLoopWithNothing 3) -> !ret
end   

let local_prev p k = begin
	let ret = ref (p.bound+1) in
  try
  for i = 0 to p.bound do
    if Info.is_reach p.heap.(i).(k) && p.scope.(i) = 3 then
			begin
       ret := i;
			 raise (EndLoopWithResult 3);
			end; 
  done;
	raise (EndLoopWithNothing 3);
	with
	| (EndLoopWithResult  3) -> !ret
	| (EndLoopWithNothing 3) -> !ret
end     
  
let get_successor p k = begin
	let ret = ref (p.bound+1)  in 
	try
  for i = 0 to p.bound do
	 if i <> k && Info.is_reach p.heap.(k).(i) then
     begin
       ret := i; 
       if i < p.gvar then
         raise (EndLoopWithResult 4);  
     end;
  done;
	raise (EndLoopWithNothing 4);
	with
	| (EndLoopWithResult 4)  -> !ret
	| (EndLoopWithNothing 4) -> !ret
end
 let result = !final_result
let successor p = p.successor

let compute_successor p = 
	let succ = Hashtbl.create (p.bound) in
for i = 0 to p.bound do
	 Hashtbl.add  succ i (get_successor p i); 
done;
  p.successor <- succ 
    
  
let update_scope p = begin
	(*update scope of local variables in p to local*)
	for i = p.gvar to p.bound do
		p.scope.(i) <- 3; (*set to private*)
	done;
  for i = 0 to p.gvar-1 do
		p.scope.(i) <- 1 (*global for the global variable*)
	done;
  let rec scope_var i = begin
	 if not (is_leaf p i) then begin
		for t = 0 to p.bound do
			if Info.is_equal p.heap.(i).(t) then
				p.scope.(t) <- p.scope.(i);
		done;
		let target_vars = next_vars p i in
		  if p.scope.(i) == 1 then 
				for k = 0 to Array.length target_vars - 1 do
				   if not (is_leaf p target_vars.(k)) then p.scope.(target_vars.(k)) <-1;
				done;
		let next_var = target_vars.(0) in
		scope_var next_var;
	end;
  end in
   for i = 3 to p.gvar-1 do
    if Label.is_elim_global p.gvars.(i-3) || Label.is_main_global p.gvars.(i-3) then scope_var i;
   done;  
	p
end

       
let copy_variable p x y = begin
	for i = 0 to p.bound do
	   p.heap.(i).(y) <- p.heap.(i).(x);
		 p.heap.(y).(i) <- p.heap.(x).(i);
	done;
	p.heap.(y).(y) <- Info.equal;
	p.scope.(y) <- p.scope.(x);
	p.data.(y) <- p.data.(x);
	p.cut.(y) <- p.cut.(x);
end

(*Kill the variable from matrix p*)
let _kill (p:t) x = begin 
  let is_merged = ref 0 in 
  for k = 3 to p.bound do
   if k <> x then 
		  if Info.is_equal p.heap.(x).(k) then is_merged := 1
  done;	
	if !is_merged == 0 then 
		begin			
		let d1,d2,d3 = p.data.(x).d1, p.data.(x).d2, p.data.(x).d3 in 	
	    for i=0 to p.bound do
		    for j=0 to p.bound do
		    	if Info.is_reach p.heap.(i).(x) && Info.is_reach p.heap.(x).(j) then
						  begin p.heap.(i).(j) <- Info.compose_two_cells p.heap.(i).(x) p.heap.(x).(j) d1 d2 d3;	end;	
	       done;
	     done;	
    end;
	for i=0 to p.bound do	
		p.heap.(x).(i) <- Info.none; 
		p.heap.(i).(x) <- Info.none; 		
	done;
  p.heap.(x).(x) <- Info.equal;
  p.data.(x)     <- {d1 = 1; d2 = 1; d3 = (0,4);};
	if x >= p.gvar then
	p.scope.(x)    <- 15;
	p.cut.(x)      <- {r1 = Info.none; d = {d1 = 15; d2 = 15; d3 = (0,4)}};
end
 

let kill_variable (lx:Label.t) p thi= 
	  let x = index p thi lx in
	let p1 = clone p in
	 _kill p1 x;
	[p1] 
    
let clean_variable p x= 
  _kill p x;
  p.data.(x) <- {d1 = 2; d2 = p.data.(x).d2; d3 = p.data.(x).d3}

let kill_variable_index x p thi= 
	let p1 = clone p in
	 _kill p1 x;
	[p1] 

let _assign' p x y = begin
  p.heap.(x).(y)  <- Info.equal;      (* adding x = y *)
	p.heap.(y).(x)  <- Info.equal;      (* adding y = x *)
	p.data.(x)  <- p.data.(y);  (* adding x.data = y.data *)
	(*In the case that x is global variable, I dont need to change its scope*)
	if p.scope.(x) <> 1 then
	  p.scope.(x) <- p.scope.(y) (* adding x.scope = y.scope *) 
	else
		p.scope.(y) <- p.scope.(x);
	p.cut.(x) <- p.cut.(y); (*dont need to assign the cut here*)
	(* Copying y *)
  for i=0 to p.bound do
    if i <> x  then begin
      p.heap.(i).(x) <- p.heap.(i).(y);
      p.heap.(x).(i) <- p.heap.(y).(i); (* diagonal *)
    end;
  done;
end


let make_new_cell (lx:Label.t) (p:t) (thi:int): t list = begin  
  let x = index p thi lx in 
  _kill p x; 
  p.scope.(x) <- 3; (*private scope*)
	p.data.(x)  <- {d1 = 1; d2 = 1; d3 = (0,4)};
  for i=0 to p.bound do 
    if i <> x then begin 
      p.heap.(i).(x) <- Info.none; 
      p.heap.(x).(i) <- Info.none; 
	  end;
  done;
  p.heap.(x).(x) <- Info.equal;
  if !example_name <> "ElimMS" && !example_name <> "Vechev" then p.heap.(x).(0) <- Info.reach_q; (*Tick*) 
  [p]
end
      
let global_lock (lx:Label.t) (p:t) (thi:int): t list = begin 
  let x = index p thi lx in 
  if snd p.data.(x).d3 = 4 then begin
    p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(x).d2; d3 = (fst p.data.(x).d3, 1)};    
    [p]
  end
  else
    []
end  

let global_unlock (lx:Label.t) (p:t) (thi:int): t list = begin  
  let x = index p thi lx in 
  if snd p.data.(x).d3 = 1 then begin
    p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(x).d2; d3 = (fst p.data.(x).d3, 4)};    
    [p]
  end
  else
    []
end    

(*This function is need to be add the case when 2 attribute point to same node*)
let next_equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x.next == y *)
		let x = index p thi lx in
		let y = index p thi ly in
		if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute  then begin
		   if Info.is_reach_one p.heap.(x).(y) then
			   [p]
		   else
         []
		end
		else
			if not (Info.is_equal p.heap.(x).(y)) then 
				[] 
		  else
				if p.cut.(x) = empty_attribute then
					[]
					else
				    [] (*not completed here*)
end

let next_inequality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x.next != y *)
		let x = index p thi lx in
		let y = index p thi ly in
		if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute  then begin
		if not (Info.is_reach_one p.heap.(x).(y)) then
			 [p] 
		 else
       []
		end
		else
			if Info.is_equal p.heap.(x).(y) 
			then 
				[]
			else
				[p]
end

let equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x == y *)
		let x,y = index p thi lx, index p thi ly in	
    if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute  then begin
      if Info.is_equal p.heap.(x).(y) || Info.is_equal p.heap.(y).(x) then
			   [p]
		   else
         []
		end
		else
			if not (Info.is_equal p.heap.(x).(y)) then 
				[] 
		  else
				[] (*not completed here*)
end  

let in_equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x != y *)
		let x,y = index p thi lx, index p thi ly in					
		if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute  then begin
		if not (Info.is_equal p.heap.(x).(y)) then begin
			 [p] end 
		 else
       []
		end
		else [p]
end

let data_equality (lx:Label.t) (d:int) p thi : t list = begin
  (* x == d *)	
	let x = index p thi lx in	
	if p.cut.(x) = empty_attribute then begin
		let new_data = p.data.(x).d1 land d in
		if  new_data <> 0 then 
			begin 
			   if new_data <> p.data.(x).d1 then 
					begin
		        (*update the data to new_data*)
						let p1 = clone p in
			      p1.data.(x) <- {d1 = new_data; d2 = p1.data.(x).d2; d3 = p.data.(x).d3;};
					  (*update data equality variables to x*)
					  for i = 0 to p.bound do
				     if Info.is_equal p1.heap.(i).(x) || Info.is_equal p1.heap.(x).(i) then 
						    p1.data.(i) <- p1.data.(x);
				    done;			   
          [p1]
			   end
			  else [p]
			end
		  else [] 
		end
	else begin
		let new_data = p.cut.(x).d.d1 land d in
		if  new_data <> 0 then 
			begin 
			   if new_data <> p.cut.(x).d.d1 then 
					begin
						let p1 = clone p in
		        (*update the data to new_data*)
			      p1.cut.(x) <- {r1 = p1.cut.(x).r1; d = {d1 = new_data; d2 = p1.cut.(x).d.d2; d3 = p1.cut.(x).d.d3}};
					  (*update data equality variables to x*)		   
          [p1]
			   end
			  else [p]
			end
		  else [] 	
	end
end

 
let lock_equality (lx:Label.t) (d:int) p thi : t list = begin
  (* x == d *)	
	let x = index p thi lx in	
	if p.cut.(x) = empty_attribute then begin
		let new_data = (0, snd p.data.(x).d3 land d) in
		if  new_data <> (0, 0) then 
			begin 
			   if new_data <> p.data.(x).d3 then 
					begin
		        (*update the data to new_data*)
			      p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(x).d2; d3 = new_data;};
					  (*update data equality variables to x*)
					  for i = 0 to p.bound do
				     if Info.is_equal p.heap.(i).(x) || Info.is_equal p.heap.(x).(i) then 
						    p.data.(i) <- p.data.(x);
				    done;			   
          [p]
			   end
			  else [p]
			end
		  else [] 
		end
	else begin
		let new_data = (0, snd p.cut.(x).d.d3 land d) in
		if  new_data <> (0,0) then 
			begin 
			   if new_data <> (0, snd p.cut.(x).d.d3) then 
					begin
		        (*update the data to new_data*)
			      p.cut.(x) <- {r1 = p.cut.(x).r1; d = {d1 = p.cut.(x).d.d1 ; d2 = p.cut.(x).d.d2; d3 = new_data;}};
					  (*update data equality variables to x*)		   
          [p]
			   end
			  else [p]
			end
		  else [] 	
	end
end										
											
let lock_inequality  (lx:Label.t) (d:int) p thi : t list = begin
   (* x <> d *)
	let x = index p thi lx in		
	if p.cut.(x) = empty_attribute then begin	
    if snd p.data.(x).d3 <> d then 
			[p]
		else
      []
	end
	else begin
		if snd p.cut.(x).d.d3 <> d then
			[p]
		else
			[]	
	end
end 								


let is_data_equality (lx:Label.t) (d:int) p thi : t list = begin
  (* x == d *)	
	let x = index p thi lx in	
	if p.cut.(x) = empty_attribute then begin
		let new_data = p.data.(x).d1 land d in
		if  new_data <> 0 then 
      [p]
		  else [] 
		end
	else begin
		let new_data = p.cut.(x).d.d1 land d in
		if  new_data <> 0 then 
			[p]
		  else [] 	
	end
end

  let color_equality (lx:Label.t) (d:int) p thi : t list = begin
  (* x == d *)	
	let x = index p thi lx in	
	if p.cut.(x) = empty_attribute then begin
		let new_data = p.data.(x).d2 land d in
		if  new_data <> 0 then 
			begin 
			   if new_data <> p.data.(x).d2 then 
					begin
		        (*update the data to new_data*)
			      p.data.(x) <- {d1 = p.data.(x).d1; d2 = new_data;d3 = p.data.(x).d3;};
					  (*update data equality variables to x*)
					  for i = 0 to p.bound do
				     if Info.is_equal p.heap.(i).(x) || Info.is_equal p.heap.(x).(i) then 
						    p.data.(i) <- p.data.(x);
				    done;			   
          [p]
			   end
			  else [p]
			end
		  else [] 
		end
	else begin
		let new_data = p.cut.(x).d.d2 land d in
		if  new_data <> 0 then 
			begin 
			   if new_data <> p.cut.(x).d.d2 then 
					begin
		        (*update the data to new_data*)
       p.cut.(x) <- {r1 = p.cut.(x).r1; d = {d1 = p.cut.(x).d.d1; d2 = new_data;d3 = p.cut.(x).d.d3;}};
					  (*update data equality variables to x*)		   
          [p]
			   end
			  else [p]
			end
		  else [] 	
	end
end

let is_color_equality (lx:Label.t) (d:int) p thi : t list = begin
  (* x == d *)	
	let x = index p thi lx in	
	if p.cut.(x) = empty_attribute then begin
		let new_data = p.data.(x).d2 land d in
		if  new_data <> 0 then 		   
          [p]
		  else [] 
		end
	else begin
		let new_data = p.cut.(x).d.d2 land d in
		if  new_data <> 0 then 
			[p]
		else 
    		[] 	
	end
end

let data_inequality  (lx:Label.t) (d:int) p thi : t list = begin
   (* x <> d *)
	let x = index p thi lx in		
	if p.cut.(x) = empty_attribute then begin	
    if p.data.(x).d1 <> d then begin
			[p]
		end
		else
      []
	end
	else begin
		if p.cut.(x).d.d1 <> d then begin
			[p]
		end
    
		else
			[]	
	end
   end

 
let color_inequality  (lx:Label.t) (d:int) p thi : t list = begin
   (* x <> d *)
	let x = index p thi lx in		
	if p.cut.(x) = empty_attribute then begin	
    if p.data.(x).d2 <> d then begin
			[p]
		end
		else
      []
	end
	else begin
		if p.cut.(x).d.d2 <> d then begin
			[p]
		end
		else
			[]	
	end
end   
   								
  
let hq_unnull_node (lx:Label.t) p thi : t list = begin
  (* x == d *)	
	let x = index p thi lx in	
	let new_data = p.data.(x).d1 land 2 in
	let color = p.data.(x).d2 in
		if  new_data <> 0 && color <> 1 then 
			begin 
			   if new_data <> p.data.(x).d1 then 
					begin			   
          [p]
			   end
			  else [p]
			end
		  else [] 
end	

let hq_null_node (lx:Label.t) p thi : t list = begin
  (* x == d *)	
	let x = index p thi lx in	
	let new_data = p.data.(x).d1 land 2 in
	let color = p.data.(x).d2 in
		if  new_data = 0 || color == 1 then 
			begin 
			   if new_data <> p.data.(x).d1 then 
					begin			   
          [p]
			   end
			  else [p]
			end
		  else [] 
end	
																																																																													    

let equal (lx:Label.t) (ly:Label.t) p thi : t list = begin
  (* x < y *)
	let x,y = index p thi lx, index p thi ly in		
	if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then begin
 	[p]
   end
	else
		[p]
end    
let in_equal (lx:Label.t) (ly:Label.t) p thi : t list = begin
  (* x < y *)
	let x,y = index p thi lx, index p thi ly in		
	if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then begin
 	[p]
   end
	else
		[p]
end  
let is_less_than (lx:Label.t) (ly:Label.t) p thi : t list = begin
  (* x < y *)
	let x,y = index p thi lx, index p thi ly in		
	if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then begin	
		if Info.get_none_ord p.heap.(x).(y) = 2  then 
			[p]
		else
      []
	end
	else
		[p]
end

let not_less_than (lx:Label.t) (ly:Label.t) p thi : t list = begin
  (* x < y *)
	let x,y = index p thi lx, index p thi ly in		
	if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then begin	
       if Info.get_none_ord p.heap.(x).(y) <> 2  then 
			[p]
		else
            []
	end
	else
	  [p]
end

let data_equality_variable (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x == y *)		
	let x,y = index p thi lx, index p thi ly in		
 if Info.get_none_ord p.heap.(x).(y) = 2 || Info.get_none_ord p.heap.(y).(x) = 2 then 
		[]
	 else begin
		p.heap.(x).(y) <- Info.data_equal;
		p.heap.(y).(x) <- Info.data_equal; 
		[p]
	end;	
end
  
 let data_inequality_variable (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x == y *)		
	let x,y = index p thi lx, index p thi ly in		
 if Info.get_none_ord p.heap.(x).(y) = 2 || Info.get_none_ord p.heap.(y).(x) = 2 then 
		[p]
	 else begin
    []
	end;	
end
  
  
let get_ord_between p x y = begin 
 
	if !example_name <> "Unordered" then begin
	 if Info.is_none_ord p.heap.(x).(y) then
		  Info.get_none_ord p.heap.(x).(y)
	 else
    2
  end    
  else	
    16    
end

let r p k = begin
	let ret = ref (p.bound+1) in
  try
  for i = 0 to p.bound do
	  if Info.is_reach p.heap.(k).(i) then
			begin
       ret := i;
			 raise (EndLoopWithResult 2);
			end; 
  done;
	raise (EndLoopWithNothing 2);
	with
	| (EndLoopWithResult  2) -> !ret
	| (EndLoopWithNothing 2) -> !ret
end



  
let is_red_cut x p = begin
	let ret = ref false in
	if p.cut.(x) <> empty_attribute then begin
	   let r1 = p.cut.(x).r1 in
		 if Info.get_beta_d2 r1 = 2 || Info.get_beta_d2 r1 = 32 then ret := true;
		 if p.cut.(x).d.d2 = 2 || p.cut.(x).d.d2 = 32 then ret := true;
	end;
	!ret
end

let is_red_cuts x p = begin
let ret = ref false in
for i = 0 to p.bound do
  if Info.is_equal p.heap.(i).(x) then
		if is_red_cut i p then ret := true;
done;
!ret
end

let rec can_be_red x p = begin
let prev_i = prev p x in
if prev_i < (p.bound + 1) then begin
   let prev_cell = p.heap.(prev_i).(x) in
	 let color = Info.get_beta_d2 prev_cell in
	 if color = 2 || p.data.(prev_i).d2 = 2 || color = 32 || p.data.(prev_i).d2 = 32 || is_red_cuts prev_i p then
		  false
	 else
		can_be_red prev_i p;
end else
  true
end



let rec can_be_red_succ x p = begin
let next_i = r p x in
if next_i < (p.bound + 1) then begin
  let next_cell = p.heap.(x).(next_i) in
	 let color = Info.get_beta_d2 next_cell in
	 if color = 2 || p.data.(next_i).d2 = 2 || color = 32 || p.data.(next_i).d2 = 32  then
		  false
	 else
		can_be_red_succ next_i p;
end else
  true
end    
  
let rec ord_between x y p = begin
let ord = ref 16 in	
if Info.is_none_ord p.heap.(x).(y) then
		  Info.get_none_ord p.heap.(x).(y)
else begin			
let next_i = r p x in
if next_i < (p.bound + 1)  then begin
  let next_cell = p.heap.(x).(next_i) in
	 let beta_ord = if Info.is_reach_more next_cell then Info.get_beta_ord next_cell land Info.get_alpha_ord next_cell else Info.get_alpha_ord next_cell in
	   if not (Info.is_equal p.heap.(next_i).(y)) then ord := beta_ord land ord_between next_i y p
		else ord := beta_ord;
		!ord
end else
	!ord
end
end  	

let is_red_cut' x p = begin
	let ret = ref false in
	if p.cut.(x) <> empty_attribute then begin
	   let r1 = p.cut.(x).r1 in
		 if Info.get_beta_d2 r1 = 2 || Info.get_beta_d2 r1 = 320 then ret := true;
		 if p.cut.(x).d.d2 = 2 || p.cut.(x).d.d2 = 320 then ret := true;
	end;
	!ret
end

let is_red_cuts' x p = begin
let ret = ref false in
for i = 0 to p.bound do
  if Info.is_equal p.heap.(i).(x) then
    if is_red_cut' i p then ret := true;
done;
!ret
end

let rec can_be_red' x p = begin
let prev_i = prev p x in
if prev_i < (p.bound + 1) then begin
   let prev_cell = p.heap.(prev_i).(x) in
	 let color = Info.get_beta_d2 prev_cell in
	 if color = 2 || p.data.(prev_i).d2 = 2 || color = 320 || p.data.(prev_i).d2 = 320 || is_red_cuts' prev_i p then
		  false
	 else
    can_be_red' prev_i p;
end else
  true
end

let rec can_be_red_succ' x p = begin
let next_i = r p x in
if next_i < (p.bound + 1) then begin
  let next_cell = p.heap.(x).(next_i) in
	 let color = Info.get_beta_d2 next_cell in
	 if color = 2 || p.data.(next_i).d2 = 2 || color = 320 || p.data.(next_i).d2 = 320  then
		  false
	 else
    can_be_red_succ' next_i p;
end else
  true
end    
  
  
let saturate_equality p k1 k2 = begin
	 p.scope.(k1) <- p.scope.(k2);
	 p.data.(k1) <- p.data.(k2);
   for i = 0 to p.bound do
		p.heap.(i).(k1) <-  p.heap.(i).(k2);
		if Info.is_equal p.heap.(i).(k1) then
			p.heap.(k1).(i) <- Info.equal;
		p.heap.(k1).(i) <-  p.heap.(k2).(i);
		if Info.is_equal p.heap.(k1).(i) then
			p.heap.(i).(k1) <- Info.equal;
	 done;
end

let remove_ord p k = begin
	 for i = 0 to p.bound do
		 if Info.is_none_ord p.heap.(k).(i) then
			  p.heap.(k).(i) <- Info.none;
		 if Info.is_none_ord p.heap.(i).(k) then
			  p.heap.(i).(k) <- Info.none;
	 done;
end
  
  let less_than (lx:Label.t) (ly:Label.t) p thi : t list = begin
 (* x < y *)
  let x,y = index p thi lx, index p thi ly in	
    (*
  if (x = 11 && !example_name = "THarris") || (x = 8 && !example_name = "MMichael") || (x = 8 && !example_name = "Vechev") || (x = 8 && !example_name = "Vechev_CAS") || (x = 8 && !example_name = "Vechev_DCAS") || (x = 8 && !example_name = "HMset1") then if (p.data.(y).d2 = 2 || p.data.(y).d2 = 32) then p.x_red <- false else  begin p.x_red <- (p.x_red && can_be_red_succ y p);end;
  if (y = 11 && !example_name = "THarris") || (y = 8 && !example_name = "MMichael") || (y = 8 && !example_name = "Vechev") || (y = 8 && !example_name = "Vechev_CAS") || (y = 8 && !example_name = "Vechev_DCAS") || (y = 8 && !example_name = "HMset1") then if (p.data.(x).d2 = 2 || p.data.(x).d2 = 32) then p.x_red <- false else begin p.x_red <- (p.x_red && can_be_red x p);end; 	
  if x = 10 then p.x_red <-  if p.data.(y).d2 = 2 || p.data.(y).d2 = 32 then false else (p.x_red && can_be_red_succ y p);
  if y = 10 then p.x_red <-  if p.data.(x).d2 = 2 || p.data.(x).d2 = 32 then false else (p.x_red && can_be_red x p);		
    *)
        
    if Label.is_new lx then begin p.x_red <-  if p.data.(y).d2 = 2 || p.data.(y).d2 = 32 then false else (p.x_red && can_be_red_succ y p); end;
      if Label.is_new ly then p.x_red <-  if p.data.(x).d2 = 2 || p.data.(x).d2 = 32 then false else (p.x_red && can_be_red x p); 
           
     if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then begin	
		if Info.get_none_ord p.heap.(x).(y) = 2  then 
			[p]
		else
	  if Info.get_none_ord p.heap.(x).(y) = 15 && Info.get_none_ord p.heap.(y).(x) = 15 then
			begin 
				p.heap.(x).(y) <- Info.update_none_ord p.heap.(x).(y) 2;
			    (*it trigers other ord relation, let update new ord relation now*)
			    for i = 0 to p.bound do
			      if Info.is_equal p.heap.(i).(y) then p.heap.(x).(i) <- Info.update_none_ord p.heap.(x).(i) 2;
			      if Info.is_equal p.heap.(i).(x) then p.heap.(i).(y) <- Info.update_none_ord p.heap.(i).(y) 2;
			    done;		 
		        [p]
			end
     else
       if Info.get_none_ord p.heap.(y).(x) = 2 then [] else 
          [p]
	end
	else begin
		[p]
	end
end
  
  
let compose_two_sets s1 s2 d1 d2 d3 = begin
	let ret = ref [||] in
	for i = 0 to Array.length s1 - 1 do
	   for j = 0 to Array.length s2 - 1 do
			ret := Array.append [|(Info.compose_two_cells s1.(i) s2.(j) d1 d2 d3)|] !ret;
		 done;
	done;
	!ret
end

let merge_cells_set s = begin
	let ret = ref [|s.(0)|] in
  for i = 1 to Array.length s - 1 do
		 let is_add = ref true in
		 let elt = s.(i) in
		 for j = 0 to Array.length !ret - 1 do
		   let p, res = Info.merge_cell elt s.(j) in
			 if res then begin !ret.(j) <- p; is_add := false;end;
		 done;
		 if !is_add then
			ret := Array.append !ret [|elt|];
	done;
	!ret
end

(*put cell in the attribute of k*)
let add_attribute p k cell = begin 
   let att = p.cut.(k) in
   if att = empty_attribute then begin
		let new_att = {r1 = cell; d = {d1 = p.data.(k).d1; d2 = p.data.(k).d2;d3 = p.data.(k).d3}} in
	  p.cut.(k) <- new_att;
   end else
    begin
     let new_cells = Info.compose_two_cells att.r1 cell p.data.(k).d1  p.data.(k).d2  p.data.(k).d3 in
     let new_att = {r1 = new_cells; d = att.d} in
     p.cut.(k) <- new_att;
   end;
end

let push_on_highway p i cell i_hw = begin 
		add_attribute p i cell;
		p.data.(i) <- {d1 = p.data.(i).d1; d2 = 0; d3 = p.data.(i).d3};
		p.heap.(i).(i_hw) <- Info.equal;
	  p.heap.(i_hw).(i) <- Info.equal;	
		saturate_equality p i i_hw;  
end
 
let compute_deleted_matrix p cut i_hw  = begin  	
let p' = clone p in	
let col = ref 0 in
let row = ref 0 in 
let m = Array.make_matrix (p'.bound+1) (p'.bound+1) 100 in
let rec compute p' k = begin
	let pre = ref (p'.bound+1) in
  for i = 0 to p'.bound do
		if Info.is_reach p'.heap.(i).(k) && not (Info.is_equal p'.heap.(i).(cut)) && p.scope.(i) = 1 then
			begin
			m.(!col).(!row) <- i;
			row := !row + 1;
			pre := i;
			end;
	done;
	if !pre < (p.bound+1) then
			begin
			col := !col + 1;
			row := 0;
			compute p' !pre;
		end
end in 
compute p' i_hw; 
let cell_array = Array.make (!col+1) Info.none in
for i = 0 to !col-1 do
  if i = 0 then 
	 begin
		let cell = p'.heap.(m.(i).(0)).(i_hw) in
		cell_array.(i) <- cell;
		for j = 0 to p'.bound do 
		 let ij = m.(i).(j) in 
		 if ij < 100 then  
		    push_on_highway p ij cell i_hw; 
		done;
	end
	else	
	begin
		let cell = Info.compose_two_cells p'.heap.(m.(i).(0)).(m.(i-1).(0)) cell_array.(i-1) p'.data.(m.(i-1).(0)).d1 p'.data.(m.(i-1).(0)).d2 p'.data.(m.(i-1).(0)).d3 in
		cell_array.(i) <- cell;
		for j = 0 to p.bound do
		 let ij = m.(i).(j) in
		 if ij < 100 then
		    push_on_highway p ij cell i_hw;
		done;
	end;
done;
end

let push_to_highway p' i_hw = begin
	let p = clone p' in
  for i = 0 to p.bound do
		if i > p.gvar && p.scope.(i) = 1 then begin
			let ret = ref 0 in
		   for j = 0 to p.bound do
			   if (Info.is_reach p.heap.(j).(i) && p.scope.(j) = 1) || (Info.is_equal p.heap.(j).(i) && i <> j && j < p.gvar) then
					ret := 1;
		   done;
			 if !ret = 0 then begin
					let cell =  p.heap.(i).(i_hw) in
					add_attribute p i cell;
			    p.heap.(i).(i_hw) <- Info.equal;
					p.heap.(i_hw).(i) <- Info.equal;
					saturate_equality p i i_hw;  
			 end;
		end;
	done;
	p
end

let dot_next_assign'_cas x y p = begin 
  (* x.next := y *)
  (*Remove previous relation of x*)
	  let new_ord =  ord_between x y p  in 
	for i = 0 to p.bound do
		if Info.is_equal p.heap.(i).(x) then
		  for j = 0 to p.bound do
	      if Info.is_reach p.heap.(i).(j) then p.heap.(i).(j) <- Info.none;
		  done;
	done;
  let p1 = clone p in
  p.heap.(x).(y) <- Info.dot_next_assign new_ord;
	if p.scope.(x) = 1 then p.scope.(y) <- p.scope.(x);
	for i = 0 to p.bound do
		if Info.is_equal p.heap.(i).(y) then p.scope.(i) <- p.scope.(y);
		for j = 0 to p.bound do
	     if (Info.is_equal p.heap.(x).(i) || Info.is_equal p.heap.(i).(x)) && (Info.is_equal p.heap.(y).(j) || Info.is_equal p.heap.(j).(y)) then
		    	p.heap.(i).(j) <- p.heap.(x).(y)		 
		done;
	done;
	let p' = clone p in
  if p'.scope.(y) = 1 && p'.scope.(x) = 1 && y > 2 then 
		begin                      		
	   compute_deleted_matrix p' x y;
  end;
	[p']; 

end

let dot_next_assign' x y p = begin
  (* x.next := y *)
  (*Remove previous relation of x*)
	(*let new_ord = if ord_between x y p = 0 then 16 else ord_between x y p in *)
	let new_ord = ord_between x y p in
	for i = 0 to p.bound do
		if Info.is_equal p.heap.(i).(x) then
		  for j = 0 to p.bound do
	      if Info.is_reach p.heap.(i).(j) then p.heap.(i).(j) <- Info.none;
		  done;
	done;
  let p1 = clone p in
  p.heap.(x).(y) <- Info.dot_next_assign new_ord;
	if p.scope.(x) = 1 then p.scope.(y) <- p.scope.(x);
	for i = 0 to p.bound do
		if Info.is_equal p.heap.(i).(y) then p.scope.(i) <- p.scope.(y);
		for j = 0 to p.bound do
	     if (Info.is_equal p.heap.(x).(i) || Info.is_equal p.heap.(i).(x)) && (Info.is_equal p.heap.(y).(j) || Info.is_equal p.heap.(j).(y)) then
		    	p.heap.(i).(j) <- p.heap.(x).(y)		 
		done;
	done;
	let p' = clone p in
  if p'.scope.(y) = 1 && p'.scope.(x) = 1 && y > 2 then 
		begin                      		
	   compute_deleted_matrix p' x y;
  end;
	[p']; 

end


let dot_next_assign'_alone x y p = begin
  (* x.next := y *)
  (*Remove previous relation of x*)
	(*let new_ord = if ord_between x y p = 0 then 16 else ord_between x y p in *)
	let new_ord = ord_between x y p in
	for i = 0 to p.bound do
		if Info.is_equal p.heap.(i).(x) then
		  for j = 0 to p.bound do
	      if Info.is_reach p.heap.(i).(j) then p.heap.(i).(j) <- Info.none;
		  done;
	done;
 p.heap.(x).(y) <- Info.dot_next_assign new_ord;
	if p.scope.(x) = 1 then p.scope.(y) <- p.scope.(x);
	for i = 0 to p.bound do
		if Info.is_equal p.heap.(i).(y) then p.scope.(i) <- p.scope.(y);
		for j = 0 to p.bound do
	     if (Info.is_equal p.heap.(x).(i) || Info.is_equal p.heap.(i).(x)) && (Info.is_equal p.heap.(y).(j) || Info.is_equal p.heap.(j).(y)) then
		    	p.heap.(i).(j) <- p.heap.(x).(y)		 
		done;
	done;
	
	[p]; 

end

let same_as_me p x = begin
	let ret = ref [||] in
	for i = 0 to p.bound do
	  if Info.is_equal p.heap.(i).(x) && i <> x then ret := Array.append !ret [|i|];
	done;
	!ret
end
 let get_next_index p x = begin
	let index = ref (p.bound+1) in
	for i = 0 to p.bound do
	  if Info.is_reach p.heap.(x).(i) then
			index := i;
	done;
  if !index <= p.bound then
	p.heap.(x).(!index), !index
	else
		Info.none, !index
 end 
   let rec get_hw_index p x =  let cell, next_x = get_next_index p x in if p.scope.(next_x) = 3 then  let cell1, next_x1 = get_hw_index p next_x in let newcell = Info.compose_two_cells cell cell1 p.data.(next_x).d1 p.data.(next_x).d2 p.data.(next_x).d3 in newcell, next_x1 else cell, next_x
     
  let reset_reach_to_none p x = begin
   for i = 0 to p.bound do	
     if Info.is_equal p.heap.(i).(x) then 
			begin
				for k = 0 to p.bound do
						if Info.is_reach p.heap.(i).(k) then p.heap.(i).(k) <- Info.none;
				done;
			end   
	 done;
  end
    let push_local_to_highway p = begin
	let ret = ref [] in
  for i = 0 to p.bound do
    if p.scope.(i) = 3 && snd (get_next_index p i) <= p.bound then begin
		  let cell, index = get_hw_index p i in
		  ret := (i, cell,index)::!ret;
		end; 
	done;
	 List.iter (fun (i,cell,index) -> let cell1 = if p.cut.(i) <> empty_attribute then Info.compose_two_cells p.cut.(i).r1 cell p.data.(i).d1 p.data.(i).d2 p.data.(i).d3
  else cell in push_on_highway p i cell1 index) !ret;
    end

let dot_next_assign (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin
  let x,y = index p thi lx, index p thi ly in
  if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then
    dot_next_assign' x y p	
  else
    if p.cut.(x) <> empty_attribute && p.cut.(y) <> empty_attribute then begin
			let p1 = clone p in
			_kill p x;
      _assign' p x y;
      [p]
     end
    else
      if p.cut.(x) <> empty_attribute && p.cut.(y) = empty_attribute  then begin

				let att = p.cut.(x) in
				_kill p x;
        _assign' p x y;
        p.cut.(x) = att;						
      [p]

      end
      else
        if p.cut.(x) = empty_attribute && p.cut.(y) <> empty_attribute then begin
          if p.bound <= 14  then 
            begin
        
					  	let same_x = same_as_me p y in
              if Array.length same_x > 0 then begin
                let p1 = clone p in
								let att = p.cut.(y) in
								_kill p y;
								(*Reset other relation of x first*)
								reset_reach_to_none p x;
					      		p.heap.(x).(y) <- Info.dot_next_assign 16; 
								for k = 0 to p.bound do
								 if Info.is_equal p.heap.(k).(x) then p.heap.(k).(y) <- Info.dot_next_assign 16;
								done;
								p.cut.(y) <- empty_attribute;
								p.data.(y) <- {d1 = att.d.d1; d2 = att.d.d2; d3 = att.d.d3};
								Array.iter (fun i -> p.heap.(y).(i) <- att.r1) same_x;
								update_scope p; 
								push_local_to_highway p;
       							[p]
						 end
              else
                begin
                  let att = p.cut.(y) in
                  reset_reach_to_none p x;  
                  p.heap.(x).(y) <- Info.reach_inv;

								for k = 0 to p.bound do
								 if Info.is_equal p.heap.(k).(x) then p.heap.(k).(y) <- Info.reach_inv;
								done;
								p.cut.(y) <- empty_attribute;
                  p.data.(y) <- {d1 = att.d.d1; d2 = att.d.d2; d3 = att.d.d3};
                  				update_scope p; 
								push_local_to_highway p;
                  [p]
                end    
				 end
				else
					[]
        end 
        else 
           []	
        
   end
   
let dot_next_assign_cas (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin
  let x,y = index p thi lx, index p thi ly in
  if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then
    dot_next_assign'_cas x y p	
  else  []	
        
   end
   
        
  let dot_next_assign_alone (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin
  let x,y = index p thi lx, index p thi ly in
  if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then
    dot_next_assign'_alone x y p	
  else 
    []		
end 
let filter_dot_next_assign (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin
  let x,y = index p thi lx, index p thi ly in
  if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then
      [p]
  else
    if p.cut.(x) <> empty_attribute && p.cut.(y) <> empty_attribute then
      [p]
    else
    [p]
end   

let data_assign (lx:Label.t) (d:int) p thi : t list = begin 	
    (* x.data := d *)
		let x = index p thi lx in
		(*in the case of no cut attribute*)
		if p.cut.(x) = empty_attribute then 
			begin	
			(*This is for normal set*)	
 if !example_name = "HMset" || !example_name = "MMichael" || !example_name = "THarris" ||  !example_name = "LazySet" ||  !example_name = "Vechev11"  then
	begin
     p.data.(x) <- {d1 = d; d2 = if d = 2 && p.data.(x).d2 = 2 then 32 else p.data.(x).d2; d3 = p.data.(x).d3}
	end
  else
		begin
		p.data.(x) <- {d1 = d; d2 = p.data.(x).d2; d3 = p.data.(x).d3}
   end;
        for i = 0 to p.bound do
			   if Info.is_equal p.heap.(i).(x) then
				  p.data.(i) <- p.data.(x);
	     done;
		end
		else begin
			let att = p.cut.(x) in 
			p.cut.(x) <- {r1 = att.r1; d = {d1 = d; d2 = att.d.d2; d3 = att.d.d3}}
		end;
	[p]
end
  
  let data_assign_variable (lx:Label.t) (ly:Label.t) p thi : t list = begin 	
    (* x.data := d *)
    let x,y = index p thi lx,index p thi ly in

    p.data.(x) <- {d1 = p.data.(y).d1; d2 =  p.data.(x).d2; d3 = p.data.(x).d3};
    []
  end
  
 
  
let set_flag p op thi = begin 
  if p.flag = Alone then 
    begin
    p.flag <-  if op = 1 then Un_cnt_rem else Cnt_un_add;
      [p]
    end else
      []
 end
  
let kill_flag p  thi = begin 
  p.flag <-  Alone;
  [p]
 end  

let kill_ret p  thi = begin 
  p.ret <-  alone_ret;
   p.interf_ret <-  alone_ret;
  [p]
 end 
  
let op_assign (lx:Label.t) (d:int) p thi : t list = begin
    (* x.data := d *)
		let x = index p thi lx in
		p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(x).d2; d3 = (0,d)};
        for i = 0 to p.bound do
			if Info.is_equal p.heap.(i).(x) then
		       p.data.(i) <- p.data.(x);
	    done;
	[p]
end  
 
 let color_var_equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x == y *)		
	let x,y = index p thi lx, index p thi ly in		
	if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then begin	
      if p.data.(x).d2 = p.data.(y).d2 then 
		[p]
	  else
		[]
    end
	else
	    []	
end 
 let strengthen_data_assign_unordered (lx:Label.t) p thi = begin
  let x = index p thi lx in
  for i = p.gvar to p.bound do
    if i <> x then _kill p i;
  done;
  compute_successor p;
	if p.threads.(0).pc = 58 then begin _kill p 8; compute_successor p; end;
  if p.cut.(x) = empty_attribute && p.data.(x).d1 land 16 = 0 then
    [p]
  else
    []
		
end    
let color_var_inequality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x == y *)		
	let x,y = index p thi lx, index p thi ly in		
	if p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute then begin	
    if p.data.(x).d2 <> p.data.(y).d2 then 
		[p]
	  else
		[]
    end
	else
	    []	
end  
   
let elim_data_assign (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x.data := d *)
		let x,y = index p thi lx,index p thi ly  in
		p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(y).d2;  d3 = p.data.(x).d3};
        for i = 0 to p.bound do
			if Info.is_equal p.heap.(i).(x) then
		       p.data.(i) <- p.data.(x);
	    done;
	[p]
end    
(*
  let get_him_success (lq:Label.t) (lh:Label.t) (lp:Label.t) (p:t) (thi:int) : t list = begin
  let iq,ih,ip = index p thi lq, index p thi lh, index p thi lp in
	let ret = ref [] in
	if Info.is_reach_more p.heap.(ih).(ip) then begin
		let data = {d1 = Info.get_beta_d1 p.heap.(ih).(ip); d2 = Info.get_beta_d2 p.heap.(ih).(ip); d3 = Info.get_beta_d3 p.heap.(ih).(ip)} in
	  let p' = clone p in
		p'.heap.(ih).(iq) <- Info.update_reach_one p.heap.(ih).(ip);
		p'.heap.(iq).(ip) <- Info.update_reach_one p.heap.(ih).(ip);
		p'.heap.(ih).(ip) <- Info.none;
		p'.data.(iq) <- data;
		ret := p'::!ret;
		let p' = clone p in
		p'.heap.(ih).(iq) <- Info.update_reach_one p.heap.(ih).(ip);
		p'.heap.(iq).(ip) <- p.heap.(ih).(ip);
		p'.heap.(ih).(ip) <- Info.none;
		p'.data.(iq) <- data;
		ret := p'::!ret;
	  let p' = clone p in
		p'.heap.(ih).(iq) <- p.heap.(ih).(ip);
		p'.heap.(iq).(ip) <- Info.update_reach_one p.heap.(ih).(ip);
		p'.heap.(ih).(ip) <- Info.none;
        p'.data.(iq) <- data;
		ret := p'::!ret;
		let p' = clone p in
		p'.heap.(ih).(iq) <- p.heap.(ih).(ip);
		p'.heap.(iq).(ip) <- p.heap.(ih).(ip);
		p'.heap.(ih).(ip) <- Info.none;
		p'.data.(iq) <- data;
		ret := p'::!ret;
	end
 else 
	if Info.is_reach_more p.heap.(ip).(5) then begin
		let data = {d1 = Info.get_beta_d1 p.heap.(ip).(5); d2 = Info.get_beta_d2 p.heap.(ip).(5); d3 = Info.get_beta_d3 p.heap.(ip).(5)} in
	  let p' = clone p in
		p'.heap.(ip).(iq) <- Info.update_reach_one p.heap.(ip).(5);
		p'.heap.(iq).(5) <- Info.update_reach_one p.heap.(ip).(5);
		p'.heap.(ip).(5) <- Info.none;
		p'.data.(iq) <- data;
		ret := p'::!ret;
		let p' = clone p in
		p'.heap.(ip).(iq) <- Info.update_reach_one p.heap.(ip).(5);
		p'.heap.(iq).(5) <- p.heap.(ip).(5);
		p'.heap.(ip).(5) <- Info.none;
		p'.data.(iq) <- data;
		ret := p'::!ret;
	  let p' = clone p in
		p'.heap.(ip).(iq) <- p.heap.(ip).(5);
		p'.heap.(iq).(5) <- Info.update_reach_one p.heap.(ip).(5);
		p'.heap.(ip).(5) <- Info.none;
		p'.data.(iq) <- data;
		ret := p'::!ret;
		let p' = clone p in
		p'.heap.(ip).(iq) <- p.heap.(ip).(5);
		p'.heap.(iq).(5) <- p.heap.(ip).(5);
		p'.heap.(ip).(5) <- Info.none;
		p'.data.(iq) <- data;
		ret := p'::!ret;
	end else
   ret := [];
  (*List.iter (fun x -> if x.data.(9).d3 = (0,4) then begin print_cons p; print_string "second"; print_cons x; end) !ret;*)
	!ret
end
    *)  

  let get_him_success (lq:Label.t) (lh:Label.t) (lp:Label.t) (p:t) (thi:int) : t list = begin
	let iq = index p thi lq in
    p.data.(iq) <- {d1 = p.data.(iq).d1; d2 = p.data.(iq).d2; d3 = ((fst p.data.(iq).d3), 8)};
    [p]
end  
  
let get_him_fail (lq:Label.t) (lh:Label.t) (lp:Label.t) (p:t) (thi:int) : t list = begin
	let iq,ih,ip = index p thi lq, index p thi lh, index p thi lp in
	if Info.is_reach_one p.heap.(ih).(ip) && Info.is_reach_one p.heap.(ip).(1) then 
	 [p]
  else
    []	
      
end
(*
  let cas_data_elim_success (x:Label.t) (d1:int) (d2:int) p thi = begin
	let cond = List.fold_left (fun acc el -> (acc @ data_equality x d1 (clone el) thi)) [] [p] in       
  let ret = List.fold_left (fun acc el -> (acc @ data_assign x d2 (clone el) thi)) [] cond in
  ret	
end  
 *) 
 
let cas_data_elim_success (lx:Label.t) (d1:int) (d2:int) p thi = begin
  let x = index p thi lx in 
  if p.data.(x).d1 land d1 <> 0 then 
    begin
      p.data.(x) <- {d1 = d2; d2 = p.data.(x).d2; d3 =  p.data.(x).d3};
      if p.bound > 14 && !example_name = "HSYstack" then begin
       
        let ret = ref [] in
        if snd p.data.(14).d3 land 8 = 8 && p.data.(14).d1 land d2 <> 0 then
          begin
            let p1 = clone p in
            (*for the case of get help*)
            p1.data.(14) <- {d1 = d2; d2 = p.data.(14).d2; d3 =  (p.data.(14).d3)};
            ret := p1::!ret;
          end
        else
        if snd p.data.(15).d3 land 8 = 8 && p.data.(15).d1 land d2 <> 0 then
          begin
            let p2 = clone p in
            p2.data.(15) <- {d1 = d2; d2 = p.data.(15).d2; d3 =  p.data.(15).d3};
            ret := p2::!ret;
          end;    
          ret := p::!ret;
        !ret
      end
			else
			      if p.bound > 13 && !example_name = "ElimMS" then begin
        let ret = ref [] in
        if snd p.data.(14).d3 land 8 = 8 && p.data.(14).d1 land d2 <> 0 then
          begin
            let p2 = clone p in       
            p2.data.(14) <- {d1 = d2; d2 = p.data.(14).d2; d3 =  p.data.(14).d3};
            ret := p2::!ret;
          end;    
          ret := p::!ret;
        !ret
      end
        else
      [p]
    end
  else
    []  
end   
let cas_data_elim_fail (x:Label.t) (d1:int) (d2:int) p thi = begin
  if List.length (data_inequality x d1 p thi) > 0 then
		[p]
	else
		[]
   
end 
let cas_data_fail (x:Label.t) (d1:int) (d2:int) p thi = begin
  if List.length (data_inequality x d1 p thi) > 0 then
		[p]
	else
		[]
   
end   
let strengthen_cas_data_elim_success (lx:Label.t) (d1:int) (d2:int) p thi = begin
	 let x = index p thi lx in 
  [p]  
end  
   let strengthen_op_assign (lx:Label.t)  p thi = begin
		(*
		 let x = index p thi lx in 
		for i = 0 to p.bound do
    if i <> x && i >= p.gvar then
		_kill p i;
	done;
	compute_successor p;
	*)
    [p]
end
   
  let op_equality (lx:Label.t) (d:int) p thi : t list = begin
 (* x == d *)	
 (*
	let x = index p thi lx in	
	let new_data = (0, snd p.data.(x).d3 land d) in
		if  new_data <> (0, 0) then 
			begin 
			   if new_data <> p.data.(x).d3 then 
					begin
		        (*update the data to new_data*)
			      p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(x).d2; d3 = new_data;};
					  (*update data equality variables to x*)
					  for i = 0 to p.bound do
				     if Info.is_equal p.heap.(i).(x) || Info.is_equal p.heap.(x).(i) then 
						    p.data.(i) <- p.data.(x);
				    done;			   
          [p]
			   end
			  else [p]
			end
		  else [] 
		end									
  *)
    [p]
  end    
let op_inequality (lx:Label.t) (d:int) p thi : t list = begin
  (* x == d *)	
	let x = index p thi lx in	
    if snd p.data.(x).d3 <> d then 
			[p]
	else
      []
end									

    
      
let color_assign (lx:Label.t) (d:int) p thi : t list = begin
    (* x.data := d *)
		let x = index p thi lx in
		(*in the case of no cut attribute*)
		   p.data.(x) <- {d1 = p.data.(x).d1; d2 = d; d3 = p.data.(x).d3};
       for i = 0 to p.bound do
			   if Info.is_equal p.heap.(i).(x) then
				  p.data.(i) <- p.data.(x);
	     done;
	[p]
end

let color_assign_variable (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x.data := d *)
		let x,y = index p thi lx,index p thi ly  in
		(*in the case of no cut attribute*)
		   p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(y).d2; d3 = p.data.(x).d3};
       for i = 0 to p.bound do
			   if Info.is_equal p.heap.(i).(x) then
				  p.data.(i) <- p.data.(x);
	     done;
	[p]
end

let data_exchange (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x.data := d *)
		let x,y = index p thi lx,index p thi ly in
		p.data.(x) <- {d1 =  p.data.(y).d1; d2 = p.data.(y).d2; d3 = p.data.(y).d3};
	[p]
end

let data_assign' x d p = begin
    (* x.data := d *)
		(*in the case of no cut attribute*)
		if p.cut.(x) = empty_attribute then 
			begin	
		   p.data.(x) <- {d1 = d; d2 = p.data.(x).d2; d3 = p.data.(x).d3};
       for i = 0 to p.bound do
			   if Info.is_equal p.heap.(i).(x) then
				  p.data.(i) <- p.data.(x);
	     done;
		end
		else begin
			let att = p.cut.(x) in
			p.cut.(x) <- {r1 = att.r1; d = {d1 = d; d2 = att.d.d2; d3 = att.d.d3}}
		end;
end

  
let mark_assign (lx:Label.t) (d:int) p thi : t list = begin
    (* x.data := d *)
		let x = index p thi lx in
		(*in the case of no cut attribute*)
		if p.cut.(x) = empty_attribute then 
			begin	
		   p.data.(x) <- {d1 = d; d2 = p.data.(x).d2; d3 = p.data.(x).d3};
       for i = 0 to p.bound do
			   if Info.is_equal p.heap.(i).(x) then
				  p.data.(i) <- p.data.(x);
	     done;
		end
		else begin
			let att = p.cut.(x) in
			p.cut.(x) <- {r1 = att.r1; d = {d1 = d; d2 = att.d.d2; d3 = att.d.d3};}
		end;
	[p]
end
  
 
let lock_acquire_success (lx:Label.t) (d:int) (interf:bool) p thi : t list = begin
    (* x.lock := d *) 
		let x = index p thi lx in
		(*in the case of no cut attribute*)
		if p.cut.(x) = empty_attribute then 
			begin	
     if (snd p.data.(x).d3 land 4 ) = 4 then begin
     p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(x).d2; d3 = ((if interf then 0 else 1),d)};         
				for i = 0 to p.bound do
			     if Info.is_equal p.heap.(i).(x) then
				      p.data.(i) <- p.data.(x);
    done;
     
				[p]
			end else
				[]
		end
		else begin
			let att = p.cut.(x) in
    if snd att.d.d3 land 4 = 4 then begin
     p.cut.(x) <- {r1 = att.r1; d = {d1 = att.d.d1; d2 = att.d.d2; d3 = ((if interf then 0 else 1),d)};};
		  [p]
			end else
				[]
		end
end

let lock_release_success (lx:Label.t) (d:int) (interf:bool) p thi : t list = begin
    (* x.lock := d *) 
		let x = index p thi lx in
		(*in the case of no cut attribute*)
		if p.cut.(x) = empty_attribute then 
			begin	
     if fst p.data.(x).d3 = 1  then begin
     p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(x).d2; d3 = (0,d)};         
				for i = 0 to p.bound do
			     if Info.is_equal p.heap.(i).(x) then
				      p.data.(i) <- p.data.(x);
	       done;
				[p]
			end else
				[]
		end
		else begin
			let att = p.cut.(x) in
			if fst att.d.d3  = 1 then begin
    p.cut.(x) <- {r1 = att.r1; d = {d1 = att.d.d1; d2 = att.d.d2; d3 = (0,d)}};
		  [p]
			end else
				[]
		end
end

let dot_next_assign_lock (x:Label.t) (y:Label.t)  p thi = begin
  let cond3 = List.fold_left (fun acc el -> (acc @ dot_next_assign x y (clone el) thi)) [] [p] in
	cond3
end

  
  
let dot_next_assign_lock_fail (x:Label.t) (y:Label.t) p thi = begin
	if List.length (lock_inequality x 1 p thi) > 0 && List.length (lock_inequality x 4 p thi) > 0 && List.length (lock_inequality x 5 p thi) > 0 then
		[p]
	else
		[]
end

let strengthen_lock_acquire (lx:Label.t) (d:int) p thi = begin
  	let x = index p thi lx in
  for i = p.gvar to p.bound do
    if i <> x then _kill p i;
  done;
  compute_successor p;
  if p.cut.(x) = empty_attribute then
		if snd p.data.(x).d3 land 4 = 0 then
			[]
		else begin
			
			[p]
  end
 
	else begin
		let att = p.cut.(x) in
		if snd att.d.d3 land 4 = 0 then
			[]
		else
			[p]
	end

end

let strengthen_lock_release (lx:Label.t) (d:int) p thi = begin
	let x = index p thi lx in
  if p.cut.(x) = empty_attribute then
		if snd p.data.(x).d3 land 1 = 0 then
			[]
		else begin
    			[p]
  end	
  
	else begin
		let att = p.cut.(x) in
		if snd att.d.d3 land 1 = 0 then
			[]
		else
			[p]
	end

end

let strengthen_dot_next_assign_lock (lx:Label.t) (ly:Label.t) p thi = begin
	let x = index p thi lx in
	if p.scope.(x) = 1 then
	[p] else []
end
  

let strengthen_dot_next_assign (lx:Label.t) (ly:Label.t) p' thi = begin
    if !example_name = "Unordered" then begin
		let x,y = index p' thi lx,index p' thi ly in
  		_kill p' 8;
  		compute_successor p';
    	if (p'.threads.(0).pc = 50 || p'.threads.(0).pc = 70) then p'.threads.(0).pc <- 18;  
	  	if (p'.threads.(0).pc = 56) then p'.threads.(0).pc <- 79;  
		if (p'.threads.(0).pc = 58) then p'.threads.(0).pc <- 77; 
		if (p'.threads.(0).pc = 80) then p'.threads.(0).pc <- 60; 
  		if p'.cut.(x) = empty_attribute then
    	  begin 
      		if p'.cut.(y) = empty_attribute then  
       			[p']
          else 
            begin
       		  [p']    
      	end    
   end
      else if Info.is_equal p'.heap.(x).(y) then [] else [p']
   end
   else
	[p']
end

let lock_acquire_fail (lx:Label.t) (d:int) p thi : t list = begin
    (* x.lock <> d *)
		let x = index p thi lx in
		(*in the case of no cut attribute*)
		if p.cut.(x) = empty_attribute then 
			begin	
		  if snd p.data.(x).d3 <> 4 then 
				[p]
			else
				[p]
		end
		else begin
			let att = p.cut.(x) in
			if snd att.d.d3 <> d then
				[p]
			else
				[]
		end;
end

let lock_release_fail (lx:Label.t) (d:int) p thi : t list = begin
    (* x.lock <> d *)
		let x = index p thi lx in
		(*in the case of no cut attribute*)
		if p.cut.(x) = empty_attribute then 
			begin	
		  if snd p.data.(x).d3 <> 1 then 
				[p]
			else
				[]
		end
		else begin
			let att = p.cut.(x) in
			if snd att.d.d3 <> d then
				[p]
			else
				[]
		end;
end

let assign_dot_next'' x y p = begin
  (*x := y.next where y is  inside the attribute*) 
  _kill p x;
	let att = p.cut.(y) in
	let c = att.r1 in
	let ret = ref [] in
	if Info.is_reach_one c then begin
   let p1 = clone p in
         p1.heap.(x).(y) <- Info.equal;
		  p1.heap.(y).(x) <- Info.equal;
   saturate_equality p1 x y;
   let p2 = clone p1 in
	p2.cut.(x) <- att;   
   p1.cut.(x) <- empty_attribute;
   [p1;p2]  
	end
  	else if Info.is_reach_more c then begin 
	    let p1 = clone p in
		  p1.heap.(x).(y) <- Info.equal;
		  p1.heap.(y).(x) <- Info.equal;
      saturate_equality p1 x y;
      let p2 = clone p1 in
			let p3 = clone p1 in
		  (*find the data of real x*)
			let color = Info.get_beta_d2 c in 
			if Info.get_beta_d2 c <> 32 && Info.get_beta_d2 c <> 2 then 
				begin
		      let new_d1,new_d2,new_d3 = Info.get_beta_d1 c, Info.get_beta_d2 c, Info.get_beta_d3 c in 
		      let c1 = Info.update_reach_one c in 
		      let new_att1 = {r1 = c1; d = {d1 = new_d1; d2 = new_d2;d3 = new_d3};} in 
		      p1.cut.(x) <- new_att1;
   		    let new_att2 = {r1 = c; d = {d1 = new_d1; d2 = new_d2;d3 = new_d3};} in 
          p2.cut.(x) <- new_att2;
		      [p1;p2]	  
			end 
			 else
				begin
					let new_d1,new_d2,new_d3 = Info.get_beta_d1 c, Info.get_beta_d2 c, Info.get_beta_d3 c in 
				  let c1 = Info.update_reach_one c in 
		      let new_att1 = {r1 = c1; d = {d1 = new_d1; d2 = color;d3 = new_d3};} in 
		      p1.cut.(x) <- new_att1;
					let c2 = Info.remove_color c in 
   		    let new_att2 = {r1 = c2; d = {d1 = new_d1; d2 = color;d3 = new_d3};} in 
          p2.cut.(x) <- new_att2;
					let c3 = c in 
   		    let new_att3 = {r1 = c3; d = {d1 = new_d1; d2 = 1; d3 = new_d3};} in 
          p3.cut.(x) <- new_att3;	
					[p1;p2;p3]						
			  end
	end
    else
       []
end

  
  
(*
let assign_dot_next'' x y p = begin
  (*x := y.next where y is  inside the attribute*) 
	_kill p x;
	let att = p.cut.(y) in
	let c = att.r1 in
	let ret = ref [] in
	if Info.is_reach_one c then begin
		  let p1 = clone p in
	      p1.heap.(x).(y) <- Info.equal;
		  p1.heap.(y).(x) <- Info.equal;
	      saturate_equality p1 x y;
   p1.cut.(x) <- empty_attribute;
          [p1]  
	end
	else if Info.is_reach_more c then begin 
	    let p1 = clone p in
		  p1.heap.(x).(y) <- Info.equal;
		  p1.heap.(y).(x) <- Info.equal;
      saturate_equality p1 x y;
      let p2 = clone p1 in
			let p3 = clone p1 in
		  (*find the data of real x*)
			if Info.get_beta_d2 c <> 32 && Info.get_beta_d2 c <> 2 then 
				begin
		      let new_d1,new_d2,new_d3 = Info.get_beta_d1 c, Info.get_beta_d2 c, Info.get_beta_d3 c in 
		      let c1 = Info.update_reach_one c in 
		      let new_att1 = {r1 = c1; d = {d1 = new_d1; d2 = new_d2;d3 = new_d3};} in 
		      p1.cut.(x) <- new_att1;
   		    let new_att2 = {r1 = c; d = {d1 = new_d1; d2 = new_d2;d3 = new_d3};} in 
          p2.cut.(x) <- new_att2;
		      [p1;p2]	  
			end 
			 else
				begin
					let new_d1,new_d2,new_d3 = Info.get_beta_d1 c, Info.get_beta_d2 c, Info.get_beta_d3 c in 
				  let c1 = Info.update_reach_one c in 
		      let new_att1 = {r1 = c1; d = {d1 = new_d1; d2 = new_d2;d3 = new_d3};} in 
		      p1.cut.(x) <- new_att1;
					let c2 = Info.remove_color c in 
   		    let new_att2 = {r1 = c2; d = {d1 = new_d1; d2 = new_d2;d3 = new_d3};} in 
          p2.cut.(x) <- new_att2;
					let c3 = c in 
   		    let new_att3 = {r1 = c3; d = {d1 = new_d1; d2 = 2; d3 = new_d3};} in 
          p3.cut.(x) <- new_att3;	
					[p1;p2;p3]						
			  end
	end
    else
       []
end
*)

(* Create a heap with two segments y -> x; x -> z and assign color for x and x -> z*)
let create_plus_heap p y x z data lock cons_left cons_right l_color r_color = begin
  let p' = clone p in
	if p'.threads.(0).pc = 42222 then begin
			 print_int (snd lock);
	print_int (snd (Info.get_beta_d3 p'.heap.(y).(x)));
	end;
	p'.scope.(x) <- p'.scope.(y);
	p'.heap.(y).(x)  <- cons_left;
	p'.heap.(x).(z) <- cons_right;
	p'.heap.(x).(z) <- Info.assign_color p'.heap.(x).(z) r_color;
	p'.data.(x) <- {d1 = data; d2 = l_color; d3 = (4,snd lock)};
	for i = 0 to p'.bound do
		if i <> y && (Info.is_equal p'.heap.(i).(y) || Info.is_equal p'.heap.(y).(i)) then
			p'.heap.(i).(x) <- p'.heap.(y).(x); 
	done;   
	for i = 0 to p'.bound do
		if i <> z && (Info.is_equal p'.heap.(i).(z) || Info.is_equal p'.heap.(z).(i)) then
			p'.heap.(x).(i) <- p'.heap.(x).(z); 
	done; 
    [p']  
      
end


let create_single_heap p y x z data lock cons_left cons_right l_color = begin
  let p' = clone p in
 	p'.scope.(x)     <- p'.scope.(y);
	p'.heap.(y).(x)  <- cons_left;
	p'.heap.(x).(z)  <- cons_right;
  p'.data.(x) <- {d1 = data; d2 = l_color; d3 = (4,snd lock)};
	for i = 0 to p'.bound do
		if i <> y && (Info.is_equal p'.heap.(i).(y) || Info.is_equal p'.heap.(y).(i)) then
			p'.heap.(i).(x) <- p'.heap.(y).(x); 
	done;   
	for i = 0 to p'.bound do
		if i <> z && (Info.is_equal p'.heap.(i).(z) || Info.is_equal p'.heap.(z).(i)) then
			p'.heap.(x).(i) <- p'.heap.(x).(z); 
	done; 
      [p']
end

  
    
let update_data p x d = begin
  p.data.(x) <- {d1 = d; d2 = p.data.(x).d2; d3 = p.data.(x).d3};
  p
end  

let update_color p x d = begin
  p.data.(x) <- {d1 = p.data.(x).d2; d2 = d; d3 = p.data.(x).d3};
  p
end 
 
let prev_create_plus_heap p y x z cons_left cons_right l_color x_color = begin
	let p' = clone p in
	p'.scope.(x) <- p'.scope.(y);
	p'.heap.(y).(x)  <- cons_left;
	p'.heap.(x).(z) <- cons_right;
	p'.data.(x) <- {d1 = p'.data.(x).d1; d2 = x_color; d3 = p'.data.(x).d3;};
	p'.heap.(y).(x) <- Info.assign_color p'.heap.(y).(x) l_color;
	for i = 0 to p'.bound do
		if i <> y && (Info.is_equal p'.heap.(i).(y) || Info.is_equal p'.heap.(y).(i)) then
			p'.heap.(i).(x) <- p'.heap.(y).(x); 
	done;   
	for i = 0 to p'.bound do
		if i <> z && (Info.is_equal p'.heap.(i).(z) || Info.is_equal p'.heap.(z).(i)) then
			p'.heap.(x).(i) <- p'.heap.(x).(z); 
	done; 
	p'
end

let prev_create_single_heap p y x z cons_left cons_right x_color = begin
	let p' = clone p in
	p'.scope.(x)     <- p'.scope.(y);
	p'.heap.(y).(x)  <- cons_left;
	p'.heap.(x).(z)  <- cons_right;
	p'.data.(x) <- {d1 = p'.data.(x).d1; d2 = x_color; d3 = p'.data.(x).d3;};
	for i = 0 to p'.bound do
		if i <> y && (Info.is_equal p'.heap.(i).(y) || Info.is_equal p'.heap.(y).(i)) then
			p'.heap.(i).(x) <- p'.heap.(y).(x); 
	done;   
	for i = 0 to p'.bound do
		if i <> z && (Info.is_equal p'.heap.(i).(z) || Info.is_equal p'.heap.(z).(i)) then
			p'.heap.(x).(i) <- p'.heap.(x).(z); 
	done; 
	p'
end

let assign_dot_next' x y p  = begin 
  (* x := y.next *)
	_kill p x;
	let c = clone p in  
	let z = ref (p.bound + 1) in
	(*Find desternitation of y and set these paths to none, it means we remove paths but keep ordring relation*)
	for i = 0 to c.bound do
       if Info.is_reach c.heap.(y).(i) then z := i; 
	done;		
	let cell = c.heap.(y).(!z) in
	(*The first case when we can put x in between y and z*)	
  if Info.is_reach_more c.heap.(y).(!z) then 
     begin 
		 (*Find desternitation of equality node as y and set these paths to none, it means we remove paths but keep ordring relation*)
	  	  for i = 0 to c.bound do
		  	  if Info.is_equal c.heap.(i).(y) then
			      for j = 0 to c.bound do
		  	       if Info.is_equal c.heap.(!z).(j) then c.heap.(i).(j) <- Info.none;
	      	  done;
	      done;
		    let cons = Info.unfold_plus cell in	
       let color = Info.get_beta_d2 cell in 
       let data = Info.get_beta_d1 cell in
			 let lock = Info.get_beta_d3 cell in
		    (*For the first case single, plus*)			   
		    let left1,right1 =  fst (fst cons),snd (fst cons)  in
		    let left2,right2 =  fst (snd cons),snd (snd cons)  in
    (*Start splitting cases depending on color*) 
				match color with
         | (*Green*)       128->  create_plus_heap c y x !z data lock left1 right1 color color @ create_single_heap c y x !z data lock left2 right2 color  
         | (*White*)       1 ->  create_plus_heap c y x !z data lock left1 right1 color color @ create_single_heap c y x !z data lock left2 right2 color          
         | (*Blue*)        4 ->  create_plus_heap c y x !z data lock left1 right1 1 color @ create_plus_heap c y x !z data lock left1 right1 color 1 @ create_single_heap c y x !z data lock left2 right2 color
         | (*Red->Blue*)   8 ->  create_plus_heap c y x !z data lock left1 right1 1 color @ create_plus_heap c y x !z data lock left1 right1 2 4;
         | (*Blue->Red*)   16 -> create_plus_heap c y x !z data lock left1 right1 1 color @create_plus_heap c y x !z data lock left1 right1 4 2;     
         | (*Red for set*) 32 -> create_plus_heap c y x !z data lock left1 right1 1 color @ (List.map ( fun k -> update_data k x 2) (create_plus_heap c y x !z data lock left1 right1 color 1) ) @ List.map (fun k -> update_data k x 2) (create_single_heap c y x !z data lock left2 right2 color) 
        | (*Red for set*) 2 ->  if !example_name = "Vechev" || !example_name = "Vechev_CAS" || !example_name = "Vechev_DCAS" || !example_name = "HMset" || !example_name = "THarris" || !example_name = "MMichael" || !example_name = "Unordered" || !example_name = "LazySet" || !example_name = "Vechev" then
          create_plus_heap c y x !z data lock left1 right1 1 color @ (List.map ( fun k -> update_data k x 1) (create_plus_heap c y x !z data lock left1 right1 color 1)) @ (List.map ( fun k -> update_data k x 1) (create_single_heap c y x !z data lock left2 right2 color)) 
        else
          create_plus_heap c y x !z data lock left1 right1 1 color @ create_plus_heap c y x !z data lock left1 right1 color 1 @ create_single_heap c y x !z data lock left2 right2 color
				| _ -> [p]	
 	end
	else 
		begin
			let newc = clone p in
			(*In this case we update x equal to !z and triger other relation*)
			newc.heap.(x).(!z) <- Info.equal;
			newc.heap.(!z).(x) <- Info.equal;
			for i=0 to p.bound do
        	 if i <> x  then 
			   begin
           		newc.heap.(i).(x) <- newc.heap.(i).(!z);
           		newc.heap.(x).(i) <- newc.heap.(!z).(i); (* diagonal *)
         	 end;
      		done;
	    	newc.data.(x)  <- newc.data.(!z);
	    	newc.scope.(x) <- newc.scope.(!z);
		  	newc.cut.(x)   <- newc.cut.(!z);
		  	[newc]
	end    
end
 
let assign_dot_prev x y z p  = begin
  (* x := y.prev *)
	_kill p x;
	let c = clone p in  	
	let cell = c.heap.(y).(z) in
	(*The first case when we can put x in between y and z*)	
  if Info.is_reach_more cell then 
     begin 
		 (*Find desternitation of equality node as y and set these paths to none, it means we remove paths but keep ordring relation*)
	  	  for i = 0 to c.bound do
		  	  if Info.is_equal c.heap.(i).(y) then
			      for j = 0 to c.bound do
		  	       if Info.is_equal c.heap.(z).(j) then c.heap.(i).(j) <- Info.none;
	      	  done;
	      done;
		    let cons = Info.prev_unfold_plus cell in	
				let color = Info.get_beta_d2 cell in 
		    (*For the first case plus, single*)			   
		    let left1,right1 =  fst (fst cons),snd (fst cons)  in
				(*For the second case single, single*)	
		    let left2,right2 =  fst (snd cons),snd (snd cons)  in
		    (*Start splitting cases depending on color*)
				match color with
				| (*White*)       1 ->  [prev_create_plus_heap c y x z left1 right1 color color; prev_create_single_heap c y x z left2 right2 color]
     		    | (*Red*)         2 ->  [prev_create_plus_heap c y x z left1 right1 1 color;prev_create_plus_heap c y x z left1 right1 color 1; prev_create_single_heap c y x z left2 right2 color] 
				| (*Blue*)        4 ->  [prev_create_plus_heap c y x z left1 right1 1 color;prev_create_plus_heap c y x z left1 right1 color 1; prev_create_single_heap c y x z left2 right2 color] 
				| (*Red->Blue*)   8 ->  [prev_create_plus_heap c y x z left1 right1 color 1;prev_create_plus_heap c y x z left1 right1 2 4;]
				| (*Blue->Red*)   16 -> [prev_create_plus_heap c y x z left1 right1 color 1;prev_create_plus_heap c y x z left1 right1 4 2;] 
  end
	else 
		begin
			let newc = clone p in
			(*In this case we update x equal to !z and triger other relation*)
			newc.heap.(x).(z) <- Info.equal;
			newc.heap.(z).(x) <- Info.equal;
			for i=0 to p.bound do
        if i <> x  then 
			   begin
           newc.heap.(i).(x) <- newc.heap.(i).(z);
           newc.heap.(x).(i) <- newc.heap.(z).(i); (* diagonal *)
         end;
      done;
	    newc.data.(x)  <- newc.data.(z);
	    newc.scope.(x) <- newc.scope.(z);
		  newc.cut.(x)   <- newc.cut.(z);
		  [newc]
	end    
end
  
let is_global (lx:Label.t) p = begin
  let x = index p 0 lx in
  if p.scope.(x) = 1 then
    true
  else
    false
end    
  
let get_path_colors p x1 y1  = begin
 let rec get_path_color ret p x y = begin
	let next = r p x in
	   if not (Info.is_equal p.heap.(x).(y)) then begin
      if (p.data.(x).d2 = 2 || Info.get_beta_d2 p.heap.(x).(next) = 2) && !ret = 1  then ret := 2
      else  
        if (p.data.(x).d2 = 4 || Info.get_beta_d2 p.heap.(x).(next) = 4) && !ret = 2 then ret := 	8
        else
					 if (p.data.(x).d2 = 4 || Info.get_beta_d2 p.heap.(x).(next) = 4) && !ret = 1 then ret := 	4
        else
          if (p.data.(x).d2 = 8 || Info.get_beta_d2 p.heap.(x).(next) = 8) && !ret = 1 then ret := 	8
          else
            ret := 1;
	       get_path_color ret p next y;
	   end;
  end in
  let ret = ref 1 in
  get_path_color ret p x1 y1;
!ret
end


let assign_dot_next_prev (lx:Label.t) (lz:Label.t) (p:t) (thi:int) : t list = begin
  let x,z = index p thi lx, index p thi lz in
  p.start_observer <- p.observer;
	let y = ref (p.bound+1) in
	for i = 0 to p.bound do
	  if Info.is_reach p.heap.(i).(0) then 
     y := i; 
	done;
	let ret = assign_dot_prev x !y z p in
	List.iter (fun n -> n.start_events <- p.events) ret;
	ret
end

let update_unordered_data_from_color p = begin
	for i = 0 to p.bound do
	  if p.data.(i).d2 = 2 then p.data.(i) <- {d1 = 1; d2 = p.data.(i).d2; d3 = p.data.(i).d3};
	done;
end	
let assign_dot_next (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin 
	let x,y = index p thi lx, index p thi ly in 
	let ret =
	if p.cut.(y) = empty_attribute then
		begin
		  let result = assign_dot_next' x y p in
      result	
		end
	else 
		assign_dot_next'' x y p
	in
	ret
end
  
let assign_self_dot_next (lx:Label.t) (p:t) (thi:int) : t list = begin 
  let x = index p thi lx in 
  let y = 2 in
	let ret =
   if p.cut.(y) = empty_attribute then
   assign_dot_next' y x p
	else 
   assign_dot_next'' y x p
	in
  List.iter (fun t ->  _assign' t x y; _kill t y;) ret;
  if Label.is_global lx then
    List.iter (fun t -> t.data.(x) <- {d1 = t.data.(x).d1; d2 = t.data.(x).d2; d3 = (1, snd t.data.(x).d3)}) ret;
  ret
end 
  
let assign_dot_next_mark x y p= begin
	if p.cut.(y) = empty_attribute then
		assign_dot_next' x y p
	else
		assign_dot_next'' x y p
end

let get_marked_assign_dot_next (lx:Label.t) (ly:Label.t) (lmark:Label.t) p thi: t list  = begin
  let x, y, m = index p thi lx, index p thi ly, index p thi lmark in	
	let ret = ref [] in
	if p.cut.(y) = empty_attribute then begin
			if p.data.(y).d1 land 1 = 1 then begin
				let p1 = clone p in 
		    p1.value_vars.(m) <-  1;
				data_assign' y 1 p1;
				ret := !ret @ assign_dot_next' x y p1
			end;
		  if p.data.(y).d1 land 2 = 2 then begin
				let p1 = clone p in 
		    p1.value_vars.(m) <-  2;
				data_assign' y 2 p1;
				ret := !ret @ assign_dot_next' x y p1
			end;
			if p.data.(y).d1 land 4 = 4 then begin
				let p1 = clone p in 
		    p1.value_vars.(m) <-  4;
				data_assign' y 4 p1;
				ret := !ret @ assign_dot_next' x y p1
			end;
			if p.data.(y).d1 land 32 = 32 then begin
				let p1 = clone p in 
		    p1.value_vars.(m) <-  32;
				data_assign' y 32 p1;
				ret := !ret @ assign_dot_next' x y p1
			end;
			!ret
 end else begin
			if p.cut.(y).d.d1 land 1 = 1 then begin
				let p1 = clone p in 
		    p1.value_vars.(m) <-  1;
				data_assign' y 1 p1;
				ret := !ret @ assign_dot_next'' x y p1
			end;
		  if p.cut.(y).d.d1 land 2 = 2 then begin
				let p1 = clone p in 
		    p1.value_vars.(m) <-  2;
				data_assign' y 2 p1;
				ret := !ret @ assign_dot_next'' x y p1
			end;
			if p.cut.(y).d.d1 land 4 = 4 then begin
				let p1 = clone p in 
		    p1.value_vars.(m) <-  4;
				data_assign' y 4 p1;
				ret := !ret @ assign_dot_next'' x y p1
			end;
			if p.cut.(y).d.d1 land 32 = 32 then begin
				let p1 = clone p in 
		    p1.value_vars.(m) <-  32;
				data_assign' y 32 p1;
				ret := !ret @ assign_dot_next'' x y p1
			end;
      !ret
 end
end


let var_data_assign (ls:Label.t) (lx:Label.t) p thi: t list  = begin
  let s, x = index p thi ls, index p thi lx in	
  let ret = ref [] in
  let data = p.data.(x).d1 in
  (*split for two case if d1 is 3*)
  if p.cut.(x) = empty_attribute then begin
    
    if data land 1 = 1 then begin
      let p1 = clone p in 
      p1.value_vars.(s) <-  1;
      data_assign' x 1 p1;
      ret := p1::!ret;		
    end;
    if data land 4 = 4 then begin
      let p2 = clone p in 
      p2.value_vars.(s) <-  4;
      data_assign' x 4 p2;	
      ret := p2::!ret;		
    end;
    if data land 2 = 2 then begin
      let p3 = clone p in 
      p3.value_vars.(s) <-  2;
      data_assign' x 2 p3;	
      ret := p3::!ret;		
    end;
    if data land 8 = 8 then begin
      let p4 = clone p in 
      p4.value_vars.(s) <-  8;
      data_assign' x 8 p4;	
      ret := p4::!ret;		
    end;
    if data land 16 = 16 then begin
      let p5 = clone p in 
      p5.value_vars.(s) <-  16;
      data_assign' x 16 p5;	
      ret := p5::!ret;		
    end;
    if data land 32 = 32 then begin
      let p6 = clone p in 
      p6.value_vars.(s) <-  32;
      data_assign' x 32 p6;	
      ret := p6::!ret;		
   end;
  end else
		begin
			 let data = p.cut.(x).d.d1 in
		if data land 1 = 1 then begin
      let p1 = clone p in 
      p1.value_vars.(s) <-  1;
      data_assign' x 1 p1;
      ret := p1::!ret;		
    end;
    if data land 4 = 4 then begin
      let p2 = clone p in 
      p2.value_vars.(s) <-  4;
      data_assign' x 4 p2;	
      ret := p2::!ret;		
    end;
    if data land 2 = 2 then begin
      let p3 = clone p in 
      p3.value_vars.(s) <-  2;
      data_assign' x 2 p3;	
      ret := p3::!ret;		
    end;
    if data land 8 = 8 then begin
      let p4 = clone p in 
      p4.value_vars.(s) <-  8;
      data_assign' x 8 p4;	
      ret := p4::!ret;		
    end;
    if data land 16 = 16 then begin
      let p5 = clone p in 
      p5.value_vars.(s) <-  16;
      data_assign' x 16 p5;	
      ret := p5::!ret;		
    end;
    if data land 32 = 32 then begin
      let p6 = clone p in 
      p6.value_vars.(s) <-  32;
      data_assign' x 32 p6;	
      ret := p6::!ret;		
   end;
  end;
  !ret
   end


let var_equality (lmark: Label.t) (d:int) p thi = begin 
  let m = index p thi lmark in	
	 if  p.value_vars.(m) = d then begin 
   if !example_name <> "LazySet" && !example_name <> "HMset" then p.value_vars.(m) <- 0;
		[p]
		end
	 else
		[]
end



let var_inequality (lmark: Label.t) (d:int) p thi = begin
   let m = index p thi lmark in	
	 if  p.value_vars.(m) <> d then begin
   if !example_name <> "LazySet" && !example_name <> "HMset" then p.value_vars.(m) <- 0;
		[p]
		end
	 else
		[]
end


let compare_matrix p = begin
  let newbound = ref p.bound in
	let cutpoint = ref 0 in
	for i = 0 to p.bound do
		if p.cut.(i) <> empty_attribute then
			cutpoint := !cutpoint + 1;
	done;
	newbound := !newbound + !cutpoint;
	let matrix = Array.make_matrix (!newbound+2) (!newbound+2) 15 in
	for i = 0 to p.bound do
		if p.cut.(i) <> empty_attribute then 
		begin
				let ord = 2 in
				if ord = 2 then begin
							matrix.(i).(i+ !cutpoint+1) <- 7;
						  matrix.(i+ !cutpoint +1).(i) <- 11;
      if Info.get_beta_ord p.cut.(i).r1 = 2 || Info.get_beta_ord p.cut.(i).r1 = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
								matrix.(!newbound+1).(i+ !cutpoint+1) <- 7;
						    matrix.(i+ !cutpoint+1).(!newbound+1) <- 11;
							end;
      if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
							end;
      if p.cut.(i).d.d2 = 2 || p.cut.(i).d.d2 = 32 then begin
							 matrix.(!newbound+1).(i+ !cutpoint +1) <- 7;
						   matrix.(i+ !cutpoint +1).(!newbound+1) <- 11;
							end;
		    end;
		end;
		for j = 0 to p.bound do
			if Info.is_reach_one p.heap.(i).(j) then
				begin
				let ord = Info.get_alpha_ord p.heap.(i).(j) in
				if ord = 2 || ord = 32 then begin
					if p.cut.(i) = empty_attribute && p.cut.(j) = empty_attribute then
						begin 
							matrix.(i).(j) <- 7;
						  matrix.(j).(i) <- 11;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j) <- 7;
						   matrix.(j).(!newbound+1) <- 11;
							end;
						end;
					if p.cut.(i) <> empty_attribute && p.cut.(j) = empty_attribute then
						begin 
							matrix.(i+ !cutpoint+1).(j) <- 7;
						  matrix.(j).(i+ !cutpoint +1) <- 11;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i + !cutpoint+1).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j) <- 7;
						   matrix.(j).(!newbound+1) <- 11;
							end;
						end;	
					if p.cut.(i) <> empty_attribute && p.cut.(j) <> empty_attribute then
						begin 
							matrix.(i+ !cutpoint+1).(j+ !cutpoint+1) <- 7;
						  matrix.(j+ !cutpoint).(i+ !cutpoint +1) <- 11;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i + !cutpoint+1).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j + !cutpoint+1) <- 7;
						   matrix.(j + !cutpoint+1).(!newbound+1) <- 11;
							end;
						end;	
					if p.cut.(i) = empty_attribute && p.cut.(j) <> empty_attribute then
						begin 
							matrix.(i).(j+ !cutpoint+1) <- 7;
						  matrix.(j+ !cutpoint+1).(i) <- 11;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j + !cutpoint+1) <- 7;
						   matrix.(j + !cutpoint+1).(!newbound+1) <- 11;
							end;
						end;	
				end;
			end;
			if Info.is_reach_more p.heap.(i).(j) then
				begin
				let ord = Info.get_beta_ord p.heap.(i).(j) land Info.get_alpha_ord p.heap.(i).(j) in
				if ord = 2 || ord = 32 then begin
					if p.cut.(i) = empty_attribute && p.cut.(j) = empty_attribute then
						begin 
							matrix.(i).(j) <- 7;
						  matrix.(j).(i) <- 11;
        if Info.get_beta_d2 p.heap.(i).(j) = 2 || Info.get_beta_d2 p.heap.(i).(j) = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
								matrix.(!newbound+1).(j) <- 7;
						    matrix.(j).(!newbound+1) <- 11;
							end;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j) <- 7;
						   matrix.(j).(!newbound+1) <- 11;
							end;
						end;
					if p.cut.(i) <> empty_attribute && p.cut.(j) = empty_attribute then
						begin 
							matrix.(i+ !cutpoint+1).(j) <- 7;
						  matrix.(j).(i+ !cutpoint +1) <- 11;
        if Info.get_beta_d2 p.heap.(i).(j) = 2 || Info.get_beta_d2 p.heap.(i).(j) = 32 then begin
							  matrix.(i+ !cutpoint+1).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 11;
								matrix.(!newbound+1).(j) <- 7;
						    matrix.(j).(!newbound+1) <- 11;
							end;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i + !cutpoint+1).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j) <- 7;
						   matrix.(j).(!newbound+1) <- 11;
							end;
						end;	
					if p.cut.(i) <> empty_attribute && p.cut.(j) <> empty_attribute then
						begin 
							matrix.(i+ !cutpoint+1).(j+ !cutpoint+1) <- 7;
						  matrix.(j+ !cutpoint).(i+ !cutpoint +1) <- 11;
        if Info.get_beta_d2 p.heap.(i).(j) = 2 || Info.get_beta_d2 p.heap.(i).(j) = 32 then begin
							  matrix.(i + !cutpoint+1).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 11;
								matrix.(!newbound+1).(j + !cutpoint+1) <- 7;
						    matrix.(j + !cutpoint+1).(!newbound) <- 11;
							end;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i + !cutpoint+1).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j + !cutpoint+1) <- 7;
						   matrix.(j + !cutpoint+1).(!newbound+1) <- 11;
							end;
						end	;
					if p.cut.(i) = empty_attribute && p.cut.(j) <> empty_attribute then
						begin 
							matrix.(i).(j+ !cutpoint+1) <- 7;
						  matrix.(j+ !cutpoint+1).(i) <- 11;
        if Info.get_beta_d2 p.heap.(i).(j) = 2 || Info.get_beta_d2 p.heap.(i).(j) = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
								matrix.(!newbound+1).(j + !cutpoint+1) <- 7;
						    matrix.(j + !cutpoint+1).(!newbound+1) <- 11;
							end;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j + !cutpoint+1) <- 7;
						   matrix.(j + !cutpoint+1).(!newbound+1) <- 11;
							end;
						end;	
				end;
			end;
			if Info.is_none_ord p.heap.(i).(j) then 
				begin
				let ord = Info.get_alpha_ord p.heap.(i).(j) in
				if ord = 2 || ord = 32 then begin
					if p.cut.(i) = empty_attribute && p.cut.(j) = empty_attribute then
						begin 
							matrix.(i).(j) <- 7;
						  matrix.(j).(i) <- 11;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j) <- 7;
						   matrix.(j).(!newbound+1) <- 11;
							end;
						end;
					if p.cut.(i) <> empty_attribute && p.cut.(j) = empty_attribute then
						begin 
							matrix.(i+ !cutpoint+1).(j) <- 7;
						  matrix.(j).(i+ !cutpoint +1) <- 11;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i + !cutpoint+1).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j) <- 7;
						   matrix.(j).(!newbound+1) <- 11;
							end;
						end	;
					if p.cut.(i) <> empty_attribute && p.cut.(j) <> empty_attribute then
						begin 
							matrix.(i+ !cutpoint+1).(j+ !cutpoint+1) <- 7;
						  matrix.(j+ !cutpoint).(i+ !cutpoint +1) <- 11;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i + !cutpoint+1).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j + !cutpoint+1) <- 7;
						   matrix.(j + !cutpoint+1).(!newbound+1) <- 11;
							end;
						end	;
					if p.cut.(i) = empty_attribute && p.cut.(j) <> empty_attribute then
						begin 
							matrix.(i).(j+ !cutpoint+1) <- 7;
						  matrix.(j+ !cutpoint+1).(i) <- 11;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i).(!newbound+1) <- 7;
						    matrix.(!newbound+1).(i) <- 11;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j + !cutpoint+1) <- 7;
						   matrix.(j + !cutpoint+1).(!newbound+1) <- 11;
							end;
						end	;
				end	;			
			end;	
			if Info.is_equal p.heap.(i).(j) then 
				begin
				let ord = Info.get_alpha_ord p.heap.(i).(j) in
				if ord = 1 then begin
					if p.cut.(i) = empty_attribute && p.cut.(j) = empty_attribute then
						begin 
							matrix.(i).(j) <- 0;
						  matrix.(j).(i) <- 0;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i).(!newbound+1) <- 0;
						    matrix.(!newbound+1).(i) <- 0;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j) <- 0;
						   matrix.(j).(!newbound+1) <- 0;
							end;
						end;
					if p.cut.(i) <> empty_attribute && p.cut.(j) = empty_attribute then
						begin 
							matrix.(i+ !cutpoint+1).(j) <- 0;
						  matrix.(j).(i+ !cutpoint +1) <- 0;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i + !cutpoint+1).(!newbound+1) <- 0;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 0;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j) <- 0;
						   matrix.(j).(!newbound+1) <- 0;
							end;
						end;	
					if p.cut.(i) <> empty_attribute && p.cut.(j) <> empty_attribute then
						begin 
							matrix.(i+ !cutpoint+1).(j+ !cutpoint+1) <- 0;
						  matrix.(j+ !cutpoint).(i+ !cutpoint +1) <- 0;
        if p.data.(j).d2 = 2 ||  p.data.(j).d2 = 32 then begin
							  matrix.(i + !cutpoint+1).(!newbound+1) <- 0;
						    matrix.(!newbound+1).(i + !cutpoint+1) <- 0;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j + !cutpoint+1) <- 0;
						   matrix.(j + !cutpoint+1).(!newbound+1) <- 0;
							end;
						end;	
					if p.cut.(i) = empty_attribute && p.cut.(j) <> empty_attribute then
						begin 
							matrix.(i).(j+ !cutpoint+1) <- 0;
						  matrix.(j+ !cutpoint+1).(i) <- 0;
        if p.data.(j).d2 = 2 || p.data.(j).d2 = 32 then begin
							  matrix.(i).(!newbound+1) <- 0;
						    matrix.(!newbound+1).(i) <- 0;
							end;
        if p.data.(i).d2 = 2 || p.data.(i).d2 = 32 then begin
							 matrix.(!newbound+1).(j + !cutpoint+1) <- 0;
						   matrix.(j + !cutpoint+1).(!newbound+1) <- 0;
							end;
						end;	
				end;
			end;	
		done;
	done;
for i = 0 to !newbound+1 do
		for j = 0 to !newbound+1 do
	   for k = 0 to !newbound + 1 do
			if matrix.(i).(j) = 15 then matrix.(i).(j) <- matrix.(i).(k) lor matrix.(k).(j);
		 done;
		done;
	done;	
	matrix
end

let equal_red (lx:Label.t) p thi : t list = begin
  (* x < y *) 
	let v = index p thi lx in
    let ord_matrix = compare_matrix p in
  if ord_matrix.(v).(Array.length ord_matrix.(0)-1) = 15 && p.x_red  then 
      [p]
    else
      []
              
end
  
let validate_ccas (lo:Label.t) (la:Label.t)  (p:t) (thi:int)  : t list  = begin 
  let o,a = index p thi lo,index p thi la in 
	 if !property_name = "shape" then
		[p]
	else begin
  match p.observer with
    | Init ->  let p1 = clone p in
               set_observer p1 S1;
               p1.data.(a) <- {d1 = p.data.(a).d1; d2 = 2;d3 = p.data.(a).d3;}; 
               [p1;p] 
							
    | S1    -> let p1 = clone p in 
		           if (p.data.(o).d2) <> 2 then begin
							   set_observer p1 Bad;
								 print_string "BAD CCAS DETECTED";
								 final_result := "NOT_VALID";
								 [p1];
							 end 
							 else begin
			           set_observer p1 Init;
                 p1.data.(a) <- {d1 = p.data.(a).d1; d2 = 1; d3 = p.data.(a).d3;}; 
                 [p1] 
							 end;
	end;
end  
  
let validate_unsuccess_ccas (lo:Label.t) (la:Label.t)  (p:t) (thi:int)  : t list  = begin 
	 if !property_name = "shape" then
		[p]
	else begin
  let o,a = index p thi lo,index p thi la in 
  match p.observer with
    | Init ->  [p] 
							
    | S1    -> let p1 = clone p in 
      if (p.data.(o).d2) = 2 then begin
							   set_observer p1 Bad;
								final_result := "NOT_VALID";
								 print_string "BAD CCAS DETECTED";
								 [p1];
							 end 
      else [p]
	end;
end    
  
let validate_help_ccas (lo:Label.t) (la:Label.t)  (p:t) (thi:int)  : t list  = begin
  let o',a = index p thi lo,index p thi la in 
	 if !property_name = "shape" then
		[p]
	else begin
	let o = ref (p.bound + 1) in 
	for i = 0 to p.bound do
	  if Info.is_reach2 p.heap.(o').(i) then 
			o := i;
	done;
  match p.observer with
    | Init ->  let p1 = clone p in
               set_observer p1 S1;
               p1.data.(a) <- {d1 = p.data.(a).d1; d2 = 2;d3 = p.data.(a).d3;}; 
               [p1;p] 
							
    | S1    -> let p1 = clone p in 
		           if !o < (p.bound + 1) && (p.data.(!o).d2) <> 2 then begin
							   set_observer p1 Bad;
								final_result := "NOT_VALID";
								 print_string "BAD CCAS DETECTED";
								 [p1];
							 end 
							 else begin
			           set_observer p1 Init;
                 p1.data.(a) <- {d1 = p.data.(a).d1; d2 = 1; d3 = p.data.(a).d3;}; 
								
	
                 [p1] 
							 end;
		|_ -> [p]		
	end;			
end  
let validate_early_contains (ret: bool) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin		
	if not ret then begin 
    if (not (Info.get_beta_d2 p.heap.(3).(4) = 2)) || Info.is_reach_one p.heap.(3).(4) then begin 
			p.ret <- {cnt = if p.ret.cnt = 16 then 2 else (p.ret.cnt lor 2); add = p.ret.add; rmv = p.ret.rmv}; 	
			match p.observer with
    	| S1 -> set_observer p Bad;  print_cons p;
				final_result := "NOT_VALID";
             print_string "=========BAD STATE==========="; 
			      [p]
			| _ -> [p]		
	   end
	  else
			[p]
	end
	else
		if ret then begin 
    if ( (Info.get_beta_d2 p.heap.(3).(4) = 2)) then begin 
			p.ret <- {cnt = if p.ret.cnt = 16 then 1 else (p.ret.cnt lor 1); add = p.ret.add; rmv = p.ret.rmv}; 	
			match p.observer with
    	| Init -> set_observer p Bad;  print_cons p;
				final_result := "NOT_VALID";
             print_string "=========BAD STATE==========="; 
			      [p]
			| _ -> [p]		
	   end
	  else
			[p]
	end
	else
		[p]
end
end


let canbe_red (lx:Label.t) (ly:Label.t)  (lz:Label.t) p thi : t list = begin
  (* x < y *) 
  let x,y,z = index p thi lx,index p thi ly,index p thi lz in
  if (*p.cut.(x) = empty_attribute && p.cut.(y) = empty_attribute*) true then begin
    if  can_be_red' y p && can_be_red_succ' z p && p.data.(y).d2 <> 2 && p.data.(z).d2 <> 2 && p.data.(y).d2 <> 329 && p.data.(z).d2 <> 329 then  begin
			[p]
			end
   else begin
     []
   end
     end
  else
    []
              
end
  
let update_contains_observer (ret: bool) (p:t) : t list  = begin 
	(*print_string "help contains";*)
    match p.observer with
     | Init -> if ret then begin 
			    let p1 = clone p in
                set_observer p1 Bad;
								final_result := "NOT_VALID";
                print_string "BAD STATE" ;
			    [p1]
              end 
              else
				[p]
    | S1 ->
      if not ret then begin 
			    let p1 = clone p in
                set_observer p1 Bad;
								final_result := "NOT_VALID";
                print_string "BAD STATE"; 
			    [p1]
              end 
              else
                [p]
    | _ -> [p]
end

let update_contains (ret: bool) (p:t)  = begin 
	  (*print_string "help contains new  ";*)
    match p.observer with
     | Init -> if ret   then begin final_result := "NOT_VALID"; print_string "BAD STATE" ; end
     | S1 -> if not ret then  begin final_result := "NOT_VALID"; print_string "BAD STATE"; end;
     | _ -> ();
end

let update_insert (ret: bool) (p:t)  = begin 
	  (*print_string "help uninsert  ";*)
    match p.observer with
     | Init -> if not ret   then  begin final_result := "NOT_VALID"; print_string "BAD STATE" ; end;
     | _ -> ();
end

let update_delete (ret: bool) (p:t)  = begin 
	  (*print_string "help undelete  ";*)
    match p.observer with
     | S1 -> if not ret  then  begin final_result := "NOT_VALID"; print_string "BAD STATE" ; end;
     | _ -> ();
end


(*////////////////////////////////////////////////////LILEARIZATION OBSERVER SET//////////////////////////////////////////////////////////////////////////*)		    
(*
let validate_insert (var:Label.t) (pcs : int list) (ret: bool) (p:t) (thi:int)  : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
  let ord_matrix = compare_matrix p in
  let v = index p thi var in 
  match p.observer with
  | Init -> 
			(*If we can push both red or white*)
    if can_be_red v p && can_be_red_succ v p && p.x_red then 
			begin
			(*the first case when we can movee to the midde state with*)	
            let p1 = clone p in
            set_observer p1 S1; 
	        p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 2;d3 = p.data.(v).d3;}; 
			for i = 0 to p.bound do
			   if Info.is_equal p1.heap.(i).(v) then
				  p1.data.(i) <- p1.data.(v);
            done; 
            (*Update observer for the contains method*)
            if List.mem (p.threads.(0).interf_pc) pcs then begin
              let p2 = update_contains_observer ret p1 in
              p::p2
            end
            else
              [p1;p]
			end else 
			 [p] 
    | _ -> [p]	
end;
end
*)
let validate_insert_unordered (var:Label.t) (pcs : int list) (ret: bool) (p:t) (thi:int)  : t list  = begin 
   if !property_name = "shape" then
		[p]
	else begin
	let ord_matrix = compare_matrix p in
  let v = index p thi var in 
  let cond = Info.get_beta_d2 p.heap.(3).(4) = 2 && (Info.get_beta_d1 p.heap.(3).(4) land 1 <> 0 || Info.get_beta_d2 p.heap.(3).(4) land 8 <> 0 || p.data.(3).d2 = 2) in
  match p.observer with
  | Init -> 
			(*If we can push both red or white*)
    if not cond then 
			begin
			(*the first case when we can movee to the midde state with*)	
            let p1 = clone p in
						     set_observer p1 S1; 
	        p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 2;d3 = p.data.(v).d3;}; 
			for i = 0 to p.bound do
			   if Info.is_equal p1.heap.(i).(v) then
				  p1.data.(i) <- p1.data.(v);
            done; 
            (*Update observer for the contains method*)
						  if List.mem (p1.threads.(0).interf_pc) pcs then begin
									p1.interf_flag <- Interf;	
									p1.interf_ret <- {cnt = if p1.interf_ret.cnt = 16 then (if ret then 1 else 2) else (p1.interf_ret.cnt lor (if ret then 1 else 2)); add = p1.interf_ret.add; rmv = p1.interf_ret.rmv};
							update_contains false p;
							end;
              [p1;p]
			end else 
			 [p] 
    | _ -> [p]	
end
end

let validate_uninsert (var:Label.t) (p:t) (thi:int)  : t list  = begin 
	  let v = index p thi var in 
		if !property_name = "shape" then
		[p]
	else begin
  let v = index p thi var in
  if p.flag = Alone && (p.data.(v).d2 = 2) then begin 
  p.ret <- {cnt = p.ret.cnt; add = if p.ret.add = 16 then 2 else (p.ret.add lor 2); rmv = p.ret.rmv};
     match p.observer with
    | Init ->   if p.data.(v).d2 = 2 || p.data.(v).d2 = 32 && p.flag = Alone then begin 
      let p1 = clone p in
			final_result := "NOT_VALID";
      print_string "==========BAD UNINSERT========="; print_cons p;
	            set_observer p1 Bad; 
			    [p1]
              end 
              else
                [p]
    | S2 ->   if p.data.(v).d2 = 2 || p.data.(v).d2 = 32  then begin 
      let p1 = clone p in 
			final_result := "NOT_VALID";
      print_string "=========BAD UNINSERT========";
	            set_observer p1 Bad; 
			    [p1]
              end 
              else
				[p]
    | _ -> [p]  
  end else [p]    
end;
end

  let validate_fixed_uninsert (var:Label.t) (p:t) (thi:int)  : t list  = begin 
			if !property_name = "shape" then
		[p]
	else begin
  let v = index p thi var in
   match p.observer with
    | Init ->   if p.data.(v).d2 = 2 || p.data.(v).d2 = 32 && p.flag = Alone then begin 
      let p1 = clone p in
			final_result := "NOT_VALID";
      print_string "==========BAD UNINSERT=========";
	            set_observer p1 Bad; 
			    [p1]
              end 
              else
                [p]
    | S2 ->   if p.data.(v).d2 = 2 || p.data.(v).d2 = 32  then begin 
      let p1 = clone p in 
			final_result := "NOT_VALID";
      print_string "=========BAD UNINSERT========";
	            set_observer p1 Bad; 
			    [p1]
              end 
              else
				[p]
    | _ -> [p]    
end;
    end
    
let validate_undelete (var:Label.t)  (p:t) (thi:int)  : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
		let ord_matrix = compare_matrix p in
      
  let v = index p thi var in 
   if p.flag = Alone && ord_matrix.(v).(Array.length ord_matrix.(0)-1) = 15 && p.x_red && can_be_red v p && can_be_red_succ v p then begin
     let p1 = clone p in 
     p1.ret <- {cnt = p1.ret.cnt; add = p1.ret.add; rmv = if p1.ret.rmv = 16 then 2 else (p1.ret.rmv lor 2)};
     match p.observer with
    | S1 ->    let ord_matrix = compare_matrix p in
	             if ord_matrix.(v).(Array.length ord_matrix.(0)-1) = 15 && p.flag = Alone then 
               begin
                 final_result := "NOT_VALID";
                 print_string "=========BAD UNDELETE========"; print_cons p1;
	               set_observer p1 Bad; 
                 [p]
               end 
							else [p]
    | _ -> [p1]  
  end else [p]   
end;
end

let validate_fixed_undelete (var:Label.t) (p:t) (thi:int)  : t list  = begin 
		if  !property_name = "shape" then
		[p]
	else begin
  let v = index p thi var in 
  match p.observer with
    | S1 ->    let ord_matrix = compare_matrix p in
	             if ord_matrix.(v).(Array.length ord_matrix.(0)-1) = 15 && p.flag = Alone then 
               begin
                 let p1 = clone p in
								final_result := "NOT_VALID";
                 print_string "=========BAD UNDELETE========"; 
	               set_observer p1 Bad; 
                 [p1]
               end 
							else [p]
    | _ -> [p]  
end    ;
  end
let validate_delete (var:Label.t) (b:bool) (h: help list) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
  let v = index p thi var in
  match p.observer with
    | Init -> if (p.cut.(v) = empty_attribute && p.data.(v).d2 = 2) || (!example_name <> "Vechev" && p.cut.(v) <> empty_attribute && (p.cut.(v).d.d2 = 2 || p.cut.(v).d.d2 = 32)) then 
			         begin 
			           let p1 = clone p in 
	               set_observer p1 Bad; 
								final_result := "NOT_VALID";
							   print_string "======== BAD DETECTED ========="; 
			           [p1]
              end 
              else
				         [p]
    | S1 -> 
      if  (!example_name = "Vechev" && p.cut.(v).d.d2 = 2) ||  (!example_name <> "Vechev" && (p.cut.(v) <> empty_attribute && p.cut.(v).d.d2 = 2)  || (p.cut.(v) = empty_attribute && p.data.(v).d2 = 32) || (p.cut.(v) = empty_attribute && p.data.(v).d2 = 2) ||  (p.cut.(v) <> empty_attribute && p.cut.(v).d.d2 = 32)) then 				
				begin 
      let p1 = clone p in 
      set_observer p1 Init ;
		      	(*HELPING THE OTHER OPERATION*)
					List.iter (fun help -> 
						 match help.op with
						| 1 (*Containts*) -> if List.mem (p.threads.(0).interf_pc) help.pc then 
       					 begin
          				            p1.interf_flag <- Interf;
                  									p1.interf_ret <- {cnt = if p1.interf_ret.cnt = 16 then (if help.ret then 1 else 2) else (p1.interf_ret.cnt lor (if help.ret then 1 else 2)); add = p1.interf_ret.add; rmv = p1.interf_ret.rmv};
																(*	p1.interf_ret <- {cnt = 3; add = p1.interf_ret.add; rmv = p1.interf_ret.rmv}; *)
																	if help.ord = 1 then
					 	                         update_contains help.ret p1;
																	 if help.ord = 2 then
					 	                         update_contains help.ret p;
																	end;
						| 2 (*Insert*)   ->  if List.mem (p.threads.(0).interf_pc) help.pc then 
																	begin
																	 p1.interf_flag <- Interf;	
																 	 p1.interf_ret <- {cnt = p1.interf_ret.cnt; add = if p1.interf_ret.add = 16 then (if help.ret then 1 else 2) else (p1.interf_ret.add lor (if help.ret then 1 else 2)); rmv = p1.interf_ret.rmv}; 
																	 if help.ord = 1 then
																		update_insert help.ret p1;
																	 if help.ord = 2 then
																		update_insert help.ret p;				
																	end;	
						| 3 (*delete*)   ->  if List.mem (p.threads.(0).interf_pc) help.pc then 
																	begin
																	 p1.interf_flag <- Interf;	
																	 p1.interf_ret <- {cnt = p1.interf_ret.cnt;add = p1.interf_ret.add; rmv = if p1.interf_ret.rmv = 16 then (if help.ret then 1 else 2) else (p1.interf_ret.rmv lor (if help.ret then 1 else 2))}; 
																	 if help.ord = 1 then
																		update_delete help.ret p1;
																	 if help.ord = 2 then
																		update_delete help.ret p;				
																	end;					
						| _ -> ()												
					) h;
					[p1]			
			  end 
        else
            [p]
    | _ -> [p]
end;
end
let validate_insert (var:Label.t) (b:bool) (h: help list) (p:t) (thi:int)  : t list  = begin 
  let v = index p thi var in 	
	if !property_name = "shape" then
		[p]
		else
	begin
  match p.observer with
  | Init -> 
	(*If we can push both red or white*)
	let ord_matrix = compare_matrix p in
    if ord_matrix.(v).(Array.length ord_matrix.(0)-1) = 15 && p.x_red && can_be_red v p && can_be_red_succ v p then 
			begin
			(*the first case when we can movee to the midde state with*)	
         let p1 = clone p in
     set_observer p1 S1; 
	       p1.data.(v) <- {d1 = p.data.(v).d1; d2 =  2; d3 = p.data.(v).d3;}; 
			   for i = 0 to p.bound do
			      if Info.is_equal p1.heap.(i).(v) then
				      p1.data.(i) <- p1.data.(v);
         done; 
         (*Update observer for the contains method*)
          (*HELPING THE OTHER OPERATION*)
					List.iter (fun help -> 
						 match help.op with
						| 1 (*Containts*) -> if List.mem (p.threads.(0).interf_pc) help.pc then 
        begin
         													p1.interf_flag <- Interf;	
																	 p1.interf_ret <- {cnt = if p1.interf_ret.cnt = 16 then (if help.ret then 1 else 2) else (p1.interf_ret.cnt lor (if help.ret then 1 else 2)); add = p1.interf_ret.add; rmv = p1.interf_ret.rmv};
																	if help.ret then print_int p1.interf_ret.cnt;
																	 if help.ord = 1 then
					 	                         update_contains help.ret p1;
																	 if help.ord = 2 then
					 	                         update_contains help.ret p;
																  end;
						| 2 (*Insert*)   ->  if List.mem (p.threads.(0).interf_pc) help.pc then 
																	begin
																	 p1.interf_flag <- Interf;	
																	 p1.interf_ret <- {cnt = p1.interf_ret.cnt; add = if p1.interf_ret.add = 16 then (if help.ret then 1 else 2) else (p1.interf_ret.add lor (if help.ret then 1 else 2)); rmv = p1.interf_ret.rmv}; 
																	 if help.ord = 1 then
																		update_insert help.ret p1;
																	 if help.ord = 2 then
																		update_insert help.ret p;				
																  end;	
						| 3 (*delete*)   ->  if List.mem (p.threads.(0).interf_pc) help.pc then
																	begin 
																	 p1.interf_flag <- Interf;
																	 p1.interf_ret <- {cnt = p1.interf_ret.cnt;add = p1.interf_ret.add; rmv = if p1.interf_ret.rmv = 16 then (if help.ret then 1 else 2) else (p1.interf_ret.rmv lor (if help.ret then 1 else 2))};
																	 if help.ord = 1 then
																		update_delete help.ret p1;
																	 if help.ord = 2 then
																		update_delete help.ret p;			
																 end;	
						| _ -> ()
               ) h; 
      [p1;p]
		end 
		else 
			[p]		
    | _ -> [p]	
	end;
end

let validate_delete_unordered (var:Label.t) (pcs : int list) (ret: bool) (p:t) (thi:int)  : t list  = begin 
  let ord_matrix = compare_matrix p in
  let v = index p thi var in 
		if  !property_name = "shape" then
		[p]
	else begin  
  let cond = (p.data.(v).d2 = 2) in
  match p.observer with
    | S1 ->  if cond then 
		begin
     		(*the first case when we can movee to the midde state with*)
     		(*remove the color*) 
     		let p1 = clone p in
    		p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 1; d3 = p.data.(v).d3;}; 
    		  for i = 0 to p.bound do
			   if Info.is_equal p1.heap.(i).(v) then
				  p1.data.(i) <- p1.data.(v);
            done; 
       set_observer p1 Init; 
    if List.mem (p1.threads.(0).interf_pc) pcs then begin
																	  p1.interf_flag <- Interf;
                  									p1.interf_ret <- {cnt = if ret then 1 else 2; add = p1.interf_ret.add; rmv = p1.interf_ret.rmv};
			 let p2 = (update_contains_observer false p1) in
     		p2
			end	
			else [p1]
       end
       else
          [p]
    | Init -> if cond then 
			begin
			(*the first case when we can movee to the midde state with*)	
            let p1 = clone p in
     		set_observer p1 Bad;
				final_result := "NOT_VALID";
     		print_string "BAD STATE";
     		[p1]
       end
    		else
      			[p]
  | _ -> [p]	
end;
end			  
		
let validate_return (op:int) (ret: bool) (p:t) (thi:int) : t list  = begin 
  let r = if ret then 1 else 2 in 
  	if !property_name = "shape" then
		[p]
	else begin
			     match op with
       | 1 -> if r land p.ret.cnt = 0 then begin final_result := "NOT_VALID"; print_string "NOT CONSISTENT CNT ";print_cons p; [p] end else [p]
    | 2 -> if r land p.ret.add = 0 then begin final_result := "NOT_VALID"; print_string "NOT CONSISTENT ADD "; [p] end else [p]
    | 3 -> if r land p.ret.rmv = 0 then begin final_result := "NOT_VALID"; print_string "NOT CONSISTENT DELETE "; print_cons p; [p] end else [p]
	| _ ->   [p]
  end;
 end 

let validate_return_new (op:int) (lv:Label.t) (ret: bool) (p:t) (thi:int) : t list  = begin 
  let r = if ret then 1 else 2 in 
    let v = index p thi lv in 
  	if !property_name = "shape" then
		[p]
   else begin
     if (can_be_red v p && can_be_red_succ v p && p.scope.(v) = 3 && p.x_red) || p.scope.(v) = 1 && (p.data.(v).d2 = 2 || p.data.(v).d2 = 32 || (p.cut.(v) <> empty_attribute && (p.data.(v).d2 = 2 || p.data.(v).d2 = 32)))  
  then begin
			     match op with
       | 1 -> if r land p.ret.cnt = 0 && p.ret.cnt <> 16 then begin final_result := "NOT_VALID"; print_string "NOT CONSISTENT CNT ";print_cons p;  end;  
      [p]
       | 2 -> if r land p.ret.add = 0 then begin final_result := "NOT_VALID"; print_string "NOT CONSISTENT ADD "; print_cons p;end; [p]
    | 3 -> if r land p.ret.rmv = 0 then begin final_result := "NOT_VALID"; print_string "NOT CONSISTENT DELETE "; print_cons p;end; [p]
    | _ ->   [p]
     end else [p]
  end;
 end 

let validate_contains (lx:Label.t) (ret: bool) (p:t) (thi:int) : t list  = begin 
  let x = index p thi lx in 
  	if !property_name = "shape" then
		[p]
   else 
     if (can_be_red x p && can_be_red_succ x p && p.scope.(x) = 3 && p.x_red) || p.scope.(x) = 1 && (p.data.(x).d2 = 2 || p.data.(x).d2 = 32 || (p.cut.(x) <> empty_attribute && (p.data.(x).d2 = 2 || p.data.(x).d2 = 32)))  
   then begin
			
	p.ret <- {cnt = if p.ret.cnt = 16 then (if ret then 1 else 2) else (p.ret.cnt lor (if ret then 1 else 2)); add = p.ret.add; rmv = p.ret.rmv};   	
       match p.observer with
         | Init -> if ret then begin print_cons p;
			    let p1 = clone p in 
                set_observer p1 Bad; 
								final_result := "NOT_VALID";
       print_string "=======BAD STATE 1======" ;
			    [p1]
              end 
              else
                [p]
    | S2 -> if ret then begin 
			    let p1 = clone p in
                set_observer p1 Bad;
								final_result := "NOT_VALID";
       print_string "==========BAD STATE 2==========" ;
			    [p1]
              end 
              else
				[p]
    | S1 ->
      if not ret then begin 
        let p1 = clone p in print_cons p;
                set_observer p1 Bad;
								final_result := "NOT_VALID";
        print_string "=========BAD STATE 32==========="; 
			    [p1]
              end 
              else
                [p]
   end 
   else
       [p]
end  

let validate_contains_local (lx:Label.t) (ret: bool) (p:t) (thi:int) : t list  = begin 
  let x = index p thi lx in 
  	if !property_name = "shape" then
		[p]
   else 
		if p.flag = Alone then begin
     if (can_be_red x p && can_be_red_succ x p && p.scope.(x) = 3 && p.x_red) || (p.cut.(x) = empty_attribute && p.scope.(x) = 1 && (p.data.(x).d2 = 2 || p.data.(x).d2 = 32) || (p.cut.(x) <> empty_attribute && p.scope.(x) = 1 && (p.cut.(x).d.d2 = 2 || p.cut.(x).d.d2 = 32)))  
   then begin

	p.ret <- {cnt = if p.ret.cnt = 16 then (if ret then 1 else 2) else (p.ret.cnt lor (if ret then 1 else 2)); add = p.ret.add; rmv = p.ret.rmv};   	
       match p.observer with
         | Init -> if ret then begin print_cons p;
			    let p1 = clone p in 
                set_observer p1 Bad; 
								final_result := "NOT_VALID";
       print_string "=======BAD STATE 1======" ;
			    [p1]
              end 
              else
                [p]
    | S2 -> if ret then begin 
			    let p1 = clone p in
                set_observer p1 Bad;
								final_result := "NOT_VALID";
       print_string "==========BAD STATE 2==========" ;
			    [p1]
              end 
              else
				[p]
    | S1 ->
      if not ret then begin 
			    let p1 = clone p in 
                set_observer p1 Bad;
								final_result := "NOT_VALID";
								print_cons p;
        print_string "=========BAD STATE 32==========="; 
			    [p1]
              end 
              else
                [p]
   end 
	else [p]
	end
   else
       [p]
end  

let validate_contains_new (lv:Label.t) (ret: bool) (h: help list) (p:t) (thi:int) : t list  = begin 
  	if !property_name = "shape" then
		[p]
	else begin
			let v = index p thi lv in	
	if p.data.(v).d2 = 2 then begin	
		
	p.ret <- {cnt = if p.ret.cnt = 16 then (if ret then 1 else 2) else ((*p.ret.cnt lor*) (if ret then 1 else 2)); add = p.ret.add; rmv = p.ret.rmv};   	
       match p.observer with
     | Init -> if ret then begin 
			    let p1 = clone p in 
                set_observer p1 Bad; 
								final_result := "NOT_VALID";
       print_string "=======BAD STATE 1======" ;
			    [p1]
              end 
              else
                [p]
    | S2 -> if ret then begin 
			    let p1 = clone p in
                set_observer p1 Bad;
								final_result := "NOT_VALID";
       print_string "==========BAD STATE 2==========" ;
			    [p1]
              end 
              else
				[p]
    | S1 ->
			 let ord_matrix = compare_matrix p in  
      if not ret &&  ord_matrix.(v).(Array.length ord_matrix.(0)-1) = 15 && p.x_red  then begin 
			    let p1 = clone p in 
                set_observer p1 Bad;
								final_result := "NOT_VALID";
        print_string "=========BAD STATE 32==========="; 
			    [p1]
              end 
              else
				[p]
	end else
		[p]
end;
end



let validate_fixed_contains (ret: bool) (p:t) (thi:int) : t list  = begin 
    	if !property_name = "shape" then
		[p]
	else begin
		p.ret <- {cnt = if p.ret.cnt = 16 then (if ret then 1 else 2) else (p.ret.cnt lor (if ret then 1 else 2)); add = p.ret.add; rmv = p.ret.rmv};
		 match p.observer with
    | Init -> if ret then begin 
			    let p1 = clone p in 
                set_observer p1 Bad; 
								final_result := "NOT_VALID"; 
      print_string "=======BAD STATE 123======" ; 
			    [p1]
              end 
              else
                [p]
    | S1 ->
              if not ret then begin 
			    let p1 = clone p in 
                set_observer p1 Bad;
								final_result := "NOT_VALID";
                print_string "=========BAD STATE 32==========="; print_cons p;
			    [p1]
              end 
              else
				[p]
end ; 
 end 


let validate_contains_alone (ret: bool) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
  if p.flag = Alone then begin 
	  p.ret <- {cnt = if p.ret.cnt = 16 then (if ret then 1 else 2) else (p.ret.cnt lor (if ret then 1 else 2)); add = p.ret.add; rmv = p.ret.rmv}; 
    match p.observer with
     | Init -> if ret then begin 
			    let p1 = clone p in print_cons p;
                set_observer p1 Bad;
								final_result := "NOT_VALID";
       print_string "=======BAD STATE 1234======" ;
			    [p1]
              end 
              else
                [p]
    | S2 -> if ret then begin 
			    let p1 = clone p in
                set_observer p1 Bad;
								final_result := "NOT_VALID";
       print_string "==========BAD STATE 2==========" ;
			    [p1]
              end 
              else
				[p]
    | S1 ->
      if not ret then begin 
        let p1 = clone p in 
                set_observer p1 Bad; 
								final_result := "NOT_VALID";
        print_string "=========BAD STATE 33==========="; 
			    [p1]
              end 
              else
				[p]
	 end else
		[p]
end;
end
  
let validate_contains_alone_new (lv:Label.t)(ret: bool) (h: help list) (p:t) (thi:int) : t list  = begin 
  	let v = index p thi lv in
		if !property_name = "shape" then
		[p]
	else begin
   if p.flag = Alone then begin 
     if p.data.(v).d2 = 2 || p.data.(v).d2 = 32 || p.cut.(v).d.d2 = 2 then begin
	  (*p.ret <- {cnt = if p.ret.cnt = 16 then (if ret then 1 else 2) else ((*p.ret.cnt lor *)(if ret then 1 else 2)); add = p.ret.add; rmv = p.ret.rmv}; *)
		
	  p.ret <- {cnt = if p.ret.cnt = 16 then (if ret then 1 else 2) else (p.ret.cnt lor (if ret then 1 else 2)); add = p.ret.add; rmv = p.ret.rmv}; 
		
    match p.observer with
     | Init -> if ret then begin 
			    let p1 = clone p in print_cons p;
                set_observer p1 Bad;
								final_result := "NOT_VALID";
       print_string "=======BAD STATE 1======" ;
			    [p1]
              end 
              else
                [p]
    | S2 -> if ret then begin 
			    let p1 = clone p in
                set_observer p1 Bad;
								final_result := "NOT_VALID";
       print_string "==========BAD STATE 2==========" ;
			    [p1]
              end 
              else
				[p]
    | S1 ->
			
      if not ret then begin 
        let p1 = clone p in 
					print_cons p1;
                set_observer p1 Bad; 
								final_result := "NOT_VALID";
        print_string "=========BAD STATE 33==========="; 
			
			    [p1]
              end 
              else
				[p]
	 end else
    [p]
   end else
     [p]
end;
end
  
let validate_contains_alone_true (lv:Label.t)(ret: bool) (h: help list) (p:t) (thi:int) : t list  = begin 
  	let v = index p thi lv in
		if !property_name = "shape" then
		[p]
	else begin
   if true then begin 
     if p.data.(v).d2 = 2 || p.data.(v).d2 = 32 then begin
	  (*p.ret <- {cnt = if p.ret.cnt = 16 then (if ret then 1 else 2) else ((*p.ret.cnt lor *)(if ret then 1 else 2)); add = p.ret.add; rmv = p.ret.rmv}; *)
		
	  p.ret <- {cnt = if p.ret.cnt = 16 then (if ret then 1 else 2) else (p.ret.cnt lor (if ret then 1 else 2)); add = p.ret.add; rmv = p.ret.rmv}; 
		
    match p.observer with
     | Init -> if ret then begin 
			    let p1 = clone p in print_cons p;
                set_observer p1 Bad;
								final_result := "NOT_VALID";
       print_string "=======BAD STATE 1======" ;
			    [p1]
              end 
              else
                [p]
    | S2 -> if ret then begin 
			    let p1 = clone p in
                set_observer p1 Bad;
								final_result := "NOT_VALID";
       print_string "==========BAD STATE 2==========" ;
			    [p1]
              end 
              else
				[p]
    | S1 ->
			
      if not ret then begin 
        let p1 = clone p in 
                set_observer p1 Bad; 
								final_result := "NOT_VALID";
        print_string "=========BAD STATE 33==========="; 
			    [p1]
              end 
              else
				[p]
	 end else
    [p]
   end else
     [p]
end;
end	
	
  
let red_seen (p:t) (thi:int) : t list  = begin 
  let color = Info.get_beta_d2 p.heap.(3).(4) in
  if color = 2 then 
    [p]
  else
   [] 
end
  
let red_not_seen (p:t) (thi:int) : t list  = begin 
  let color = Info.get_beta_d2 p.heap.(3).(4) in
  if color <> 2 then 
    [p]
  else
   [] 
end  
  
  
let validate_operation (lv:Label.t) (p:t) (ops:string) (op:string) (thi:int) : t list  = begin 
	  let v = index p thi lv in 
		 if !property_name = "shape" then
		[p]
	else begin
		match p.observer with
		|  Init -> let p1 = clone p in
	             set_observer p1 S1; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 2;d3 = p.data.(v).d3;}; (*Push the RED (2)*)
							 (*update for other equaliti indicies*)
							 for i = 0 to p1.bound do
							  if Info.is_equal p1.heap.(i).(v) then 
									p1.data.(i) <- p1.data.(v);
							 done;
							 [p;p1]
		| S1 -> let p1 = clone p in
	             set_observer p1 S2; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 4;d3 = p.data.(v).d3;}; (*Push the BLUE (4)*)
							 (*update for other equaliti indicies*)
							 for i = 0 to p1.bound do
							  if i <> v && Info.is_equal p1.heap.(i).(v) then 
									p1.data.(i) <- p1.data.(v);
							 done; 
							 [p;p1]
		| _ -> [p]
	end;
end
  
    
(*////////////////////////////////////////////////////LILEARIZATION OBSERVER AND STACK//////////////////////////////////////////////////////////////////////////*)

(*FILO*)
let validate_push (lv:Label.t) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
	  let v = index p thi lv in 
		match p.observer with
		|  Init -> let p1 = clone p in
	             set_observer p1 S1; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 2;d3 = p.data.(v).d3;}; (*Push the RED (2)*)
							 (*update for other equaliti indicies*)
							 for i = 0 to p1.bound do
							  if Info.is_equal p1.heap.(i).(v) then 
									p1.data.(i) <- p1.data.(v);
							 done;
							 [p;p1]
		| S1 -> let p1 = clone p in
	             set_observer p1 S2; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 4;d3 = p.data.(v).d3;}; (*Push the BLUE (4)*)
							 (*update for other equaliti indicies*)
							 for i = 0 to p1.bound do
							  if i <> v && Info.is_equal p1.heap.(i).(v) then 
									p1.data.(i) <- p1.data.(v);
							 done; 
							 [p;p1]
		| _ -> [p]
end;
end
let validate_pop (lv:Label.t) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
	  let v = index p thi lv in 
		match p.observer with
		| Init -> if p.data.(v).d2 = 2 || p.data.(v).d2 = 4 then 
			          begin
			           set_observer p Bad;
								 [p]
							end else
							   [p]
		|  S1 -> if p.data.(v).d2 = 4 then
							begin
								set_observer p Happy;
								[p]
						 end else
  				if p.data.(v).d2 = 2 then
							begin
								set_observer p Init;
								[p]
						 end  else [p]
		|  S2 -> if p.data.(v).d2 = 4 then
             begin
	             set_observer p Happy; 
						   [p];
							end
						 else if 	p.data.(v).d2 = 2 then
							begin
								set_observer p Bad;
								final_result := "NOT_VALID";
         print_string "BAD OBSERVER 3";
         print_cons p; 
         exit 0;
								[p]
						 end else [p]
		| _ -> [p]
end;
end
let validate_pop_empty (lv:Label.t) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
	  let v = index p thi lv in 
		match p.observer with
		|  S1 -> if p.data.(v).d2 = 2 then
							begin
								set_observer p Bad;
								final_result := "NOT_VALID";
								print_string "BAD POP EMPTY"; 
								[p]
						 end else [p]
		| _ -> [p]
end;
end

(*EX FILO*)
let validate_ex_push_pop (lv:Label.t) (p:t) (thi:int) : t list  = begin  
           if p.bound > 3332 then
           print_cons p;
		if !property_name = "shape" then
		[p]
	else begin
  let v = index p thi lv in 
  let lin_ex_pop c = begin 
     match p.observer with 
	| Init -> if c = 2 || c = 4 then 
			          begin
               set_observer p Bad;
                [p]
							end else
							   [p]
 |  S1 -> if c = 2 then
							begin
         set_observer p Init;
         p.data.(v) <- {d1 = p.data.(v).d1; d2 = 2; d3 = p.data.(v).d3};
        (*update for the helped guy*) 
         if p.bound > 14 && p.data.(14).d1 = 2 && List.mem (p.threads.(0).interf_pc) [31;51;52;54;56] && p.threads.(0).pc = 40 then begin
           let p1 = clone p in
           p1.data.(14) <- {d1 = p.data.(14).d1; d2 = 2; d3 = p.data.(14).d3};
           [p;p1]
         end else
       
								[p]
						 end else
         if c = 4  then
							begin
         set_observer p Happy;
         p.data.(v) <- {d1 = p.data.(v).d1; d2 = 4; d3 = p.data.(v).d3}; 
								
								(*update for the helped guy*) 
         if p.bound > 14 && p.data.(14).d1 = 2 && List.mem (p.threads.(0).interf_pc) [31;51;52;54;56] && p.threads.(0).pc = 40 then begin
           let p1 = clone p in
           p1.data.(14) <- {d1 = p.data.(14).d1; d2 = 2; d3 = p.data.(14).d3};
           [p;p1]
         end else
       
								[p]
						 end else [p]
		|  S2 -> if c = 4 then
             begin
               set_observer p Happy; 
               p.data.(v) <- {d1 = p.data.(v).d1; d2 = 4; d3 = p.data.(v).d3};
						(*update for the helped guy*) 
         if p.bound > 14 && p.data.(14).d1 = 2 && List.mem (p.threads.(0).interf_pc) [31;51;52;54;56] && p.threads.(0).pc = 40 then begin
           let p1 = clone p in
           p1.data.(14) <- {d1 = p.data.(14).d1; d2 = 4; d3 = p.data.(14).d3};
           [p;p1]
         end else
       
								[p]
							end
						 else if c = 2 then
							begin
								set_observer p S3;
								final_result := "NOT_VALID";
								print_string "BAD OBSERVER 3"; 
								(*update for the helped guy*) 
         if p.bound > 14 && p.data.(14).d1 = 2 && List.mem (p.threads.(0).interf_pc) [31;51;52;54;56] && p.threads.(0).pc = 40 then begin
           let p1 = clone p in
           p1.data.(14) <- {d1 = p.data.(14).d1; d2 = 2; d3 = p.data.(14).d3};
           [p;p1]
         end else
       
								[p]
						 end else [p]
		| _ -> [p]
		end in
		
		match p.observer with
		| Init -> let p' = clone p in
			        set_observer p S1; 
							(*RED*)
              p'::lin_ex_pop 2
		| S1 ->   let p' = clone p in
			        set_observer p S2;
			        (*BLUE*) 
							p'::lin_ex_pop 4
		| S2 -> [p]
end;
end
(*EX LOSS*)
(* 
let lin_ex_push_pop (lv:Label.t) (p:t) (thi:int) : t list  = begin 
	  let lin_ex_pop c = begin
		match p.observer with
		| Init -> if c = 2 then 
			          begin
			          set_observer p S3;
								print_string "BAD OBSERVER 3"; 
								 [p]
							end else
							   [p]
		| _ -> [p]
		end in
		match p.observer with
	|  Init -> let p1 = clone p in
	             set_observer p1 Happy; 
							 [p;p1]
		| _ -> [p]
end

(*////////////////////////////////////////////////////LILEARIZATION OBSERVER QUEUE//////////////////////////////////////////////////////////////////////////*)
*)
 
	 let validate_enqueue (var:Label.t) (p:t) (thi:int) : t list  = begin 
			if !property_name = "shape" then
		[p]
	else begin
	  let v = index p thi var in 
		if !example_name = "HWqueue" then begin
		   if p.bound >= 6 && ((p.threads.(0).pc = 111 && p.threads.(0).interf_pc == 111) || 
     (p.threads.(0).pc = 111 && (p.threads.(0).interf_pc == 103 ||  p.threads.(0).interf_pc == 104))) then [p]
		else begin 
		match p.observer with
		|  Init -> let p1 = clone p in
	             set_observer p1 S1; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 2;d3 = p.data.(v).d3;}; (*Push the RED*)
							 (*update for other equaliti indicies*)
							 for i = 0 to p1.bound do
							  if Info.is_equal p1.heap.(i).(v) then 
									p1.data.(i) <- p1.data.(v);
							 done;
							 [p;p1]
		| S1 -> let p1 = clone p in
	             set_observer p1 S2; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 4;d3 = p.data.(v).d3}; (*Push the BLUE*)
							 (*update for other equaliti indicies*)
							 for i = 0 to p1.bound do
							  if i <> v && Info.is_equal p1.heap.(i).(v) then 
									p1.data.(i) <- p1.data.(v);
							 done;
                  [p;p1]
         | _  -> [p] 
		end;
		end 
		else 
			begin
		match p.observer with
		|  Init -> let p1 = clone p in
	             set_observer p1 S1; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 2;d3 = p.data.(v).d3;}; (*Push the RED*)
							 p1.events <- Array.append p1.events [|2|];
							 (*update for other equaliti indicies*)
							 for i = 0 to p1.bound do
							  if Info.is_equal p1.heap.(i).(v) then 
									p1.data.(i) <- p1.data.(v);
							 done;
							 [p;p1]
		| S1 -> let p1 = clone p in
	             set_observer p1 S2; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 4;d3 = p.data.(v).d3;}; (*Push the BLUE*)
							 p1.events <- Array.append p1.events [|4|]; 
							 (*update for other equaliti indicies*)
							 for i = 0 to p1.bound do
							  if i <> v && Info.is_equal p1.heap.(i).(v) then 
									p1.data.(i) <- p1.data.(v);
							 done;
                  [p;p1]
         | _  -> [p] 
		end		
end;
end
let validate_dequeue (var:Label.t) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
	 if !example_name = "ElimMS" then begin
		 let v = index p thi var in 
		match p.observer with 
		| Init -> if p.data.(v).d2 = 2 || p.data.(v).d2 = 4 then 
			          begin
			                     set_observer p S3;
													final_result := "NOT_VALID";
								 print_string "BAD OBSERVER 1"; 
								 [p]
							end else
							   [p]
		|  S1 -> if p.data.(v).d2 = 2 then (*Dequeue the RED*)
			        begin
	                     set_observer p Init; 
											p.events <- Array.append p.events [|12|];
						   [p];
							end
                 else if p.data.(v).d2 = 4 then (*Can not dequeue BLUE*)
					begin
						 set_observer p Bad;
						final_result := "NOT_VALID";
						 print_string "BAD OBSERVER 2 "; 
						 [p]
                 end else [p]
       |  S2 -> if p.data.(v).d2 = 2 then (*RED*) 
            begin 
              set_observer p Happy;        
							p.events <- Array.append p.events [|12|];               
						   [p];
							end
                 else if p.data.(v).d2 = 4 then (*BLUE*)
                   begin 
                      print_cons p;
                     set_observer p Bad; 
                     print_string " BAD "; 
                    
								[p]
                   end else [p]
				| Happy -> 		 if p.data.(v).d2 = 2 then 	p.events <- Array.append p.events [|12|]
				 else if p.data.(v).d2 = 4 then 	p.events <- Array.append p.events [|14|];  	
         [p]
		| _ -> [p]
	 end else begin
	  let v = index p thi var in 
		match p.observer with 
		| Init -> if p.data.(v).d2 = 2 || p.data.(v).d2 = 4 then 
			          begin
			                     set_observer p S3;
													final_result := "NOT_VALID";
								 print_string "BAD OBSERVER 1"; 
								 [p]
							end else
							   [p]
		|  S1 -> if p.data.(v).d2 = 2 then (*Dequeue the RED*)
			        begin
	                     set_observer p Happy; 
						   [p];
							end
                 else if p.data.(v).d2 = 4 then (*Can not dequeue BLUE*)
					begin
						 set_observer p Bad;
						final_result := "NOT_VALID";
						 print_string "BAD OBSERVER 2 "; 
						 [p]
                 end else [p]
       |  S2 -> if p.data.(v).d2 = 2 then (*RED*) 
            begin 
              set_observer p Happy;                       
						   [p];
							end
                 else if p.data.(v).d2 = 4 then (*BLUE*)
                   begin 
                      print_cons p;
                     set_observer p Bad; 
										final_result := "NOT_VALID";
                     print_string " BAD "; 
								[p]
                   end else [p]
		| _ -> [p]
	end
end;
end

let validate_call_enqueue (var:Label.t)  (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
	  let v = index p thi var in 
		match p.observer with
		|  Init -> let p1 = clone p in
	             set_observer p1 S1; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 2;d3 = p.data.(v).d3;}; (*Push the RED*)
							 [p;p1]
		|  S2 -> let p1 = clone p in
	             set_observer p1 S3; 
							 p1.data.(v) <- {d1 = p.data.(v).d1; d2 = 4;d3 = p.data.(v).d3;}; (*Push the BLUE*)
							 (*update for other equaliti indicies*)
							 for i = 0 to p1.bound do
							  if Info.is_equal p1.heap.(i).(v) then 
									p1.data.(i) <- p1.data.(v);
							 done;
							 [p;p1]
    | _  -> [p] 
end ;
end

let validate_ret_enqueue (var:Label.t) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
	  let v = index p thi var in 
		match p.observer with
    |  S1 -> if p.data.(v).d2 = 2 then begin
	               set_observer p S2; 							
      [p]
    end else begin
      set_observer p Happy;
      [p]
    end
    |  S3 -> if p.data.(v).d2 = 4 then begin
	               set_observer p S4; 							
     [p]
       end else begin
         set_observer p Happy;
         [p]
       end
    
    | Init  -> [p]
    | _  -> set_observer p Happy;[p] 
end ;
end
let validate_ret_dequeue (var:Label.t) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
	  let v = index p thi var in 
		match p.observer with
		|  S4 -> if p.data.(v).d2 = 4 then
								begin
	               set_observer p Bad;
								final_result := "NOT_VALID";
          print_string "BAD HWSTATE "; 
          [p]
        end
  else begin	
     set_observer p Happy;					
      [p]
    end;
    | _  -> if p.data.(v).d2 = 4 || p.data.(v).d2 = 2 then
								begin
	               set_observer p Happy;
							  end;							
							 [p]
end ;
end
let validate_dequeue_empty (var:Label.t) (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
  let v = index p thi var in 
		match p.observer with
		|  S1 -> if p.data.(v).d2 = 1 then
				begin
				  set_observer p Bad;
					final_result := "NOT_VALID";
				  print_string "BAD EMPTY";
				  [p]
		end else [p]
		| _ -> [p]
end;
end


let execute_event o e = begin
	match e with
	| 1 -> o
	| 2 -> if o = Init then S1 else o
	| 4 -> if o = S1 then S2 else o
	| 12 -> if o = S1 || o = S2 then Happy else if o = Init then Bad else o
	| 14 -> if o = Init || o = S1 || o = S2 then Bad else o
	| _ -> o
end

let execute_events_seq o e = begin
	let ret = ref o in
	Array.iter (fun e' -> (ret := execute_event !ret e')) e;
	!ret
end

let validate_ex_enqueue_dequeue (p:t) (thi:int) : t list  = begin 
		if !property_name = "shape" then
		[p]
	else begin
	let obs = p.start_observer in
	let enq_color = match obs with
	                | Init -> 2
									| S1 -> 4
									| _ -> 1
	in
	let deq_color = if enq_color <> 1 then 10 + enq_color else enq_color in
	let end_events = Array.sub p.events (Array.length p.start_events) (Array.length p.events - Array.length p.start_events) in
	let seq_events = Array.append (Array.append p.start_events [|enq_color|]) (Array.append end_events [|deq_color|]) in
	let ret_obs = execute_events_seq obs seq_events in
	if ret_obs = Bad then
	p.events <- seq_events;
	p.observer <- ret_obs;	
	if p.bound > 14 && p.data.(15).d1 = 2 && List.mem (p.threads.(0).interf_pc) [7;9;10;8;40]  then begin
           let p1 = clone p in
           p1.data.(14) <- {d1 = p.data.(14).d1; d2 = enq_color; d3 = p.data.(14).d3};
           [p;p1]
  end else      
					 [p]
end	;
end
		  
let nothing (p:t) (thi:int) : t list = [p]

let empty (p:t) (thi:int) : t list = []

let hq_deq_strengthen (lx:Label.t) (p:t) (thi:int) : t list = 
	let x = index p thi lx in
	if p.data.(x).d1 <> 1 then
		[p]
	else
		[]

let check_commit listp = begin
  List.iter (fun p -> if p.observer = S3 then print_string "REAL BAD") listp;
  listp
end  


let assign (lx:Label.t) (ly:Label.t) p thi : t list = begin 
  (* x := y *) 
 let x,y = index p thi lx, index p thi ly in
  _kill p x;
	_assign' p x y;
	update_scope p;
  [p]
end

let reach (lx:Label.t) (ly:Label.t) p thi : t list = begin
  (* x := y *)
  let x,y = index p thi lx, index p thi ly in
  if Info.is_reach_more p.heap.(x).(y) then
  [p]
	else
		[]
end

let unreach (lx:Label.t) (ly:Label.t) p thi : t list = begin
  (* x := y *)
  let x,y = index p thi lx, index p thi ly in
  if not (Info.is_reach_more p.heap.(x).(y)) then
  [p]
	else
		[]
end


let reach_one (lx:Label.t) (ly:Label.t) p thi : t list = begin
  (* x := y *)
  let x,y = index p thi lx, index p thi ly in
  if Info.is_reach p.heap.(x).(y) then
  [p]
	else
		[]
end

let attempt_mark (x:Label.t) (y:Label.t) (d:int) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ data_equality x d (clone el) thi)) [] [p] in
	let cond2 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] cond1 in         
  let cond3 = List.fold_left (fun acc el -> (acc @ data_assign x 2 (clone el) thi)) [] cond2  in
cond3
end
  
(*This is for lockfree in the art of multiprocessor and michael*)

let strengthen_mark (x:Label.t) (y:Label.t) (d:int) p1 thi = begin
	if !example_name = "THarris" then begin
	  _kill p1 7;
	  _kill p1 6;
   compute_successor p1;
	end
  else	
    _kill p1 5;
 	
(*
	let x',y' = index p thi x, index p thi y in
	for i = 0 to p.bound do
	  if i <> x' && i <> y' & i >= p.gvar then _kill p i;
	done;
	compute_successor p;*)
	let cond1 = List.fold_left (fun acc el -> (acc @ data_equality x d (clone el) thi)) [] [p1] in
	let cond2 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] cond1 in         
  cond2    
end
 
let filter_mark (lx:Label.t) (ly:Label.t) (d:int) p thi = begin
  let x,y = index p thi lx,index p thi ly in 
  if p.cut.(x) <> empty_attribute || (p.cut.(y) = empty_attribute && p.data.(x).d1 land d <> 0) then
    []
  else
    [p]   
end  
  
let filter_cas_set (lx:Label.t) (ly:Label.t) (d:int) p thi = begin
  let x,y = index p thi lx,index p thi ly in 
  if p.cut.(x) <> empty_attribute || p.cut.(y) <> empty_attribute || (p.cut.(x) = empty_attribute && p.data.(x).d1 land d <> 0) then
    []
  else
    [p]   
end  
  
let filter_dcas_set (lx:Label.t) (ly:Label.t) (lz:Label.t) p thi = begin
  let x,y,z = index p thi lx,index p thi ly,index p thi lz in 
  if p.cut.(x) <> empty_attribute || p.cut.(y) <> empty_attribute || (p.cut.(z) <> empty_attribute) then
    []
  else
    [p]   
end  	

let ccas_equality (lx:Label.t) (ly:Label.t) p thi = begin
	  let x,y = index p thi lx, index p thi ly in
		if p.data.(x).d1 land p.data.(y).d1 <> 0 then begin
		   if Info.is_equal p.heap.(x).(y) then
				[p]
			 else
				begin
					if not (x = 3 && y = 4) then begin 
					p.heap.(x).(y) <- Info.equal;
					p.heap.(y).(x) <- Info.equal; 
					p.data.(y) <- p.data.(x); 		
					[p]
					end
					else
						[]
			end
		end
		else
			[]
end

let ccas_inequality (lx:Label.t) (ly:Label.t) p thi = begin
	  let x,y = index p thi lx, index p thi ly in
		if p.data.(x).d1 land p.data.(y).d1 = 0 then 
		   [p]
		else
		begin
			if Info.is_equal p.heap.(x).(y) then []
			else
				[p]
		end
end

let ccas_assign (lx:Label.t) (ly:Label.t) p thi = begin
	  let x,y = index p thi lx, index p thi ly in
		_kill p x;
		p.heap.(x).(y) <- Info.equal;
		p.heap.(y).(x) <- Info.equal;
		p.data.(x) <- p.data.(y);
		saturate_equality p x y;
		[p]
end

let ccas_assign' x y p thi = begin
		_kill p x;
		p.heap.(x).(y) <- Info.equal;
		p.heap.(y).(x) <- Info.equal;
		p.data.(x) <- p.data.(y);
		saturate_equality p x y;
		[p]
end

let ccas_success (lr:Label.t) (la:Label.t) (lo:Label.t) (ld:Label.t) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ ccas_assign lr la (clone el) thi)) [] [p] in
	let cond2 = List.fold_left (fun acc el -> (acc @ ccas_equality la lo (clone el) thi)) [] cond1 in       
  let cond3 = List.fold_left (fun acc el -> (acc @ ccas_assign la ld   (clone el) thi)) [] cond2 in		
	if p.threads.(0).pc = 32 then print_cons (List.nth cond3 0);
	cond3
end	  

let create_desc (lx:Label.t) (lo:Label.t) (ln:Label.t) p thi = begin
  let x,o,n = index p thi lx, index p thi lo, index p thi ln in
	p.data.(x) <- {d1 = 2; d2 = p.data.(x).d2; d3 = p.data.(x).d3};
	p.heap.(x).(n) <- Info.reach1;
	p.heap.(x).(o) <- Info.reach2; 
	[p]
end

let create_desc_rdcss (ld:Label.t) (la:Label.t) (lo:Label.t) (ln:Label.t) (lc:Label.t) (le:Label.t) p thi = begin
  let d,a,o,n,c,e = index p thi ld, index p thi la, index p thi lo, index p thi ln, index p thi lc, index p thi le in
	p.data.(d) <- {d1 = 2; d2 = p.data.(d).d2; d3 = p.data.(d).d3};
	p.heap.(d).(n) <- Info.reach1;
	p.heap.(d).(o) <- Info.reach2;
	p.heap.(d).(a) <- Info.reach_a;
	p.heap.(d).(c) <- Info.reach_c;
	p.heap.(c).(e) <- Info.reach1; 
	[p]
end

let ccas_success_new (la:Label.t) (ld:Label.t) p thi = begin
	let a,d = index p thi la, index p thi ld in
	let n = ref (p.bound + 1) in 
	for i = 0 to p.bound do
	  if Info.is_reach1 p.heap.(d).(i) then begin
			n := i;end;
	done;
	let cond1 = List.fold_left (fun acc el -> (acc @ ccas_equality la ld (clone el) thi)) [] [p] in
  let cond2 = List.fold_left (fun acc el -> (acc @ ccas_assign' a !n (clone el) thi)) [] cond1 in	
	cond2
end	  

let ccas_success_old (la:Label.t) (ld:Label.t) p thi = begin
	let a,d = index p thi la, index p thi ld in
	let n = ref (p.bound + 1) in
	for i = 0 to p.bound do
	  if Info.is_reach2 p.heap.(d).(i) then
			n := i;
	done;
	let cond1 = List.fold_left (fun acc el -> (acc @ ccas_equality la ld (clone el) thi)) [] [p] in
  let cond2 = List.fold_left (fun acc el -> (acc @ ccas_assign' a !n   (clone el) thi)) [] cond1 in		
	cond2
end	  

let ccas_help_success_new (la:Label.t) (ld:Label.t) p thi = begin
	let a,d = index p thi la, index p thi ld in 
	let n = ref (p.bound + 1) in 
	for i = 0 to p.bound do
	  if Info.is_reach1 p.heap.(d).(i) then begin
			n := i; print_int i;end;
	done;
	let cond1 = List.fold_left (fun acc el -> (acc @ ccas_equality la ld (clone el) thi)) [] [p] in
  let cond2 = List.fold_left (fun acc el -> (acc @ ccas_assign' a !n   (clone el) thi)) [] cond1 in		
	cond2
end	  

let ccas_help_success_old (la:Label.t) (ld:Label.t) p thi = begin
	let a,d = index p thi la, index p thi ld in
	let n = ref (p.bound + 1) in
	for i = 0 to p.bound do
	  if Info.is_reach2 p.heap.(d).(i) then
			n := i;
	done;
	let cond1 = List.fold_left (fun acc el -> (acc @ ccas_equality la ld (clone el) thi)) [] [p] in
  let cond2 = List.fold_left (fun acc el -> (acc @ ccas_assign' a !n   (clone el) thi)) [] cond1 in		
	cond2
end	 
												
let ccas_fail (lr:Label.t) (la:Label.t) (lo:Label.t) (ld:Label.t)  p thi= begin
	 if List.length (ccas_inequality la lo p thi) > 0 then
		begin
		ccas_assign lr la p thi
		end
	else
		[] 
end	 	
let get_scope (lx:Label.t) p thi = begin
  let x = index p thi lx in 
  p.scope.(x);
end  	
	
let attempt_mark_fail (x:Label.t) (y:Label.t) (d:int) p thi = begin
 if List.length (data_inequality x d p thi) > 0 || List.length (next_inequality x y p thi) > 0 then
		[p]
	else
		[] 
end

let cas_success_set (x:Label.t) (y:Label.t) (d:int) (z:Label.t) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ data_equality x d (clone el) thi)) [] [p] in
	let cond2 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] cond1 in       
  let cond3 = List.fold_left (fun acc el -> (acc @ dot_next_assign_cas x z (clone el) thi)) [] cond2 in		
		cond3
end

let dcas_success_set (x:Label.t) (y:Label.t) (z:Label.t) (t:Label.t) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] [p] in
	let cond2 = List.fold_left (fun acc el -> (acc @ next_equality y z (clone el) thi)) [] cond1 in       
  let cond3 = List.fold_left (fun acc el -> (acc @ dot_next_assign y t (clone el) thi)) [] cond2 in		
  let cond4 = List.fold_left (fun acc el -> (acc @ dot_next_assign x z (clone el) thi)) [] cond3 in	
  if List.length cond4 > 1110 then begin
    print_string "ban dau"; print_cons p; print_string "ket qua 0"; List.iter (fun x -> print_cons x) cond3; print_string "ket qua"; List.iter (fun x -> print_cons x) cond4;	
  end;  
    cond4
end

let cas_multi_set_success (x:Label.t) (d1:int) (d2:int) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ data_equality x d1 (clone el) thi)) [] [p] in  
  let cond2 = List.fold_left (fun acc el -> (acc @ data_assign x d2 (clone el) thi)) [] cond1 in		
	cond2
end

let dot_next_unmarked_equality (x:Label.t) (y:Label.t) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ data_equality x 1 (clone el) thi)) [] [p] in
	let cond2 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] cond1 in       
    cond2
end
      
let in_dot_next_unmarked_equality (x:Label.t) (y:Label.t)p thi = begin
	if List.length (data_inequality x 1 p thi) > 0 || List.length (next_inequality x y p thi) > 0 then
		[p]
	else
		[]
end

let strengthen_dot_next_unmarked_equality (x:Label.t) (y:Label.t) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ data_equality x 1 (clone el) thi)) [] [p] in
	let cond2 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] cond1 in        
  cond2   
end
      
let cas_success (x:Label.t) (y:Label.t) (z:Label.t) p thi = begin
	let cond = List.fold_left (fun acc el -> (acc @ equality x y (clone el) thi)) [] [p] in    
		if p.threads.(0).pc = 43 && p.data.(8).d2 = 222 && p.bound < 12 then  begin print_string "FIRST...........    "; print_cons p; end;
 
  let ret = List.fold_left (fun acc el -> (acc @ assign x z (clone el) thi)) [] cond in
  ret	
end
  
let cas_data_success (x:Label.t) (d1:int) (d2:int) p thi = begin
	let cond = List.fold_left (fun acc el -> (acc @ data_equality x d1 (clone el) thi)) [] [p] in       
  let ret = List.fold_left (fun acc el -> (acc @ data_assign x d2 (clone el) thi)) [] cond in
  ret	
end  
  
  
let strengthen_cas_data_success (lx:Label.t) (d1:int) (d2:int) p thi = begin
  
  let x = index p thi lx in
  for i = p.gvar to p.bound do
    if i <> x then _kill p i;
  done;
  compute_successor p;
  if p.cut.(x) = empty_attribute && p.data.(x).d1 land 1 = 1 &&  p.data.(x).d1 land d2 <> d2 then
    [p]
  else
    []
end    
let cas_fail (x:Label.t) (y:Label.t) (z:Label.t) p thi = begin
	if List.length (in_equality x y p thi) > 0 then
		[p]
	else
		[]
end

let cas_next_success (x:Label.t) (y:Label.t) (z:Label.t) p thi = begin
  List.fold_left (fun acc el -> acc @ (dot_next_assign x z (clone el) thi)) [] (next_equality x y p thi)
end

let cas_next_fail (x:Label.t) (y:Label.t) (z:Label.t) p thi = begin
if List.length (next_inequality x y p thi) > 0 then
		[p]
	else
[]
end    
  
let cas_success_set_mark (x:Label.t) (y:Label.t) (d:int) (z:Label.t) p thi = begin
	let cond0 =  List.fold_left (fun acc el -> (acc @ data_assign y 2 (clone el) thi)) [] [p] in
	let cond1 = List.fold_left (fun acc el -> (acc @ data_equality x d (clone el) thi)) [] cond0 in
	let cond2 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] cond1 in  
	let cond3 = List.fold_left (fun acc el -> (acc @ assign_dot_next z y (clone el) thi)) [] cond2 in  	     
    let cond4 = List.fold_left (fun acc el -> (acc @ dot_next_assign x z (clone el) thi)) [] cond3 in
	cond4
end


let strengthen_cas_success_set (x:Label.t) (y:Label.t) (d:int) (z:Label.t) p thi = begin
  if !example_name = "HMse22t" && (*( p.threads.(0).pc = 23)   then set_pc p 0 14;*) ( p.threads.(0).pc = 75)   then set_pc p 0 44;
  if !example_name = "MMichael" && (p.threads.(0).pc = 23) then set_pc p 0 14;
  let cond1 = List.fold_left (fun acc el -> (acc @ data_equality x d (clone el) thi)) [] [p] in
  let cond2 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] cond1 in        
  cond2   
end

let strengthen_dcas_success_set (x:Label.t) (y:Label.t)  (z:Label.t) (t:Label.t) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] [p] in
	let cond2 = List.fold_left (fun acc el -> (acc @ next_equality y z (clone el) thi)) [] cond1 in        
  cond2   
end

let strengthen_cas_success (x:Label.t) (y:Label.t) (z:Label.t) p thi = begin
	
	let p' = clone p in
	for i = p.gvar+1 to p'.bound do
    if i <> index p' thi x && i <> index p' thi y && i <> index p' thi z then
      _kill p' i;
  done;
	if p.threads.(0).pc = 9 && !example_name = "ElimMS" then p.threads.(0).pc <- 108;
  let cond = List.fold_left (fun acc el -> (acc @ equality x y (clone el) thi)) [] [p'] in
 cond
end
  
let strengthen_fail (x:Label.t) (y:Label.t) (z:Label.t) p thi = begin
  []
end  
    
let strengthen_cas_next_success (x:Label.t) (y:Label.t) (z:Label.t) p thi = begin
 (* p.threads.(0).pc <- 1000; *)
	let cond = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] [p] in
	cond
end 
  
let strengthen_cas_success_set_mark (x:Label.t) (y:Label.t) (d:int) (z:Label.t) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ data_equality x d (clone el) thi)) [] [p] in
	let cond2 = List.fold_left (fun acc el -> (acc @ next_equality x y (clone el) thi)) [] cond1 in        
  cond2   
end

let cas_fail_set (x:Label.t) (y:Label.t) (d:int) (z:Label.t) p thi = begin
	if List.length (data_inequality x d p thi) > 0 || List.length (next_inequality x y p thi) > 0 then
		[p]
	else
		[]
end
  
let dcas_fail_set (x:Label.t) (y:Label.t) (z:Label.t) p thi = begin
	if List.length (next_inequality x y p thi) > 0 || List.length (next_inequality y z p thi) > 0 then
		[p]
	else
		[]
end
	  
let harris_check (l:Label.t) (r:Label.t) (ln:Label.t) (t:Label.t) p thi = begin
	let cond1 = List.fold_left (fun acc el -> (acc @ in_equality r t (clone el) thi)) [] [p] in
  let cond2 = List.fold_left (fun acc el -> (acc @ equality ln r (clone el) thi)) [] cond1 in
  let cond3 = List.fold_left (fun acc el -> (acc @ data_inequality r 2 (clone el) thi)) [] cond2 in  
  let cond4 = List.fold_left (fun acc el -> (acc @ color_equality r 2 (clone el) thi)) [] cond3 in     
    cond2
end

(*
let insert_elim (p1:Label.t) (temp:Label.t) (eHead:Label.t) p thi  = begin  
  (*let cond1 = List.fold_left (fun acc el -> (acc @ op_assign p1 4 (clone el) thi)) [] [p] in*)
  let cond2 = List.fold_left (fun acc el -> (acc @ assign_dot_next temp eHead (clone el) thi)) [] [p] in
  let cond3 = List.fold_left (fun acc el -> (acc @ dot_next_assign p1 temp (clone el) thi)) [] cond2 in  
  let cond4 = List.fold_left (fun acc el -> (acc @ dot_next_assign eHead p1 (clone el) thi)) [] cond3 in  
  let cond5 = List.fold_left (fun acc el -> (acc @ kill_variable temp (clone el) thi)) [] cond4 in     
  cond5
end   
  *)  
  
  
let insert_elim (p1:Label.t) (eHead:Label.t) p thi  = begin 
  let x = index p thi p1 in  
  p.data.(x) <- {d1 = p.data.(x).d1; d2 = p.data.(x).d2; d3 = ((fst p.data.(x).d3), 8)};
    [p]
end   
  
  
let start_point p = begin
let p'  = clone p in
for i = p'.gvar to p'.bound do
  _kill p' i;
done;
if Info.is_reach p'.heap.(4).(3) then 4
else
	3
end
  
 

  
let rec compute_signiture_prev p k = begin
  let s = String.make (p.bound+1) '0' in
 String.set s k '1'; 
 for i = 0 to p.bound do
   if Info.is_equal p.heap.(i).(k) then
     String.set s i '1';
    let color =  string_of_int (p.data.(i).d2) in
   let unique =  string_of_int (fst p.data.(i).d3) in
     let cut_color = if p.cut.(i) <> empty_attribute then string_of_int (p.cut.(i).d.d2) else "Emp" in
	   let cut_beta_color = if p.cut.(i) <> empty_attribute then string_of_int (Info.get_beta_d2 p.cut.(i).r1) else "EmpBetaColor" in
     let cut_r = if p.cut.(i) <> empty_attribute then string_of_int (Info.get_relation p.cut.(i).r1) else "EmpCut" in
		 Buffer.add_string key color;
     Buffer.add_string key cut_color;
	   Buffer.add_string key cut_beta_color;
   Buffer.add_string key cut_r;
 done;
  Buffer.add_string key s; 
 let i = local_prev p k in
  if i < (p.bound+1) && p.scope.(i) = 3 then begin
 if Info.is_reach_one p.heap.(i).(k) then
   begin
     Buffer.add_string key "1";
  	 compute_signiture_prev p i;
	 end
	else
	 if Info.is_reach_more p.heap.(i).(k) then
    begin
      let color = string_of_int (Info.get_beta_d2 p.heap.(i).(k)) in
      Buffer.add_string key "2";
      Buffer.add_string key color;
		 compute_signiture_prev p i;	
		end
end;
end
  
let rec compute_signiture p k = begin
 Buffer.add_string key (string_of_state (p.observer));
 Buffer.add_string key (string_of_flag (p.flag));
 Buffer.add_string key "bret";
 Buffer.add_string key (string_of_int (p.ret.cnt));
 Buffer.add_string key ";";
 Buffer.add_string key (string_of_int (p.ret.add));
 Buffer.add_string key ";";
 Buffer.add_string key (string_of_int (p.ret.rmv));
 Buffer.add_string key "eret";
 Buffer.add_string key (if Array.length (p.value_vars) > 0 then string_of_int (p.value_vars.(0)) else "");
 let s = String.make (p.bound+1) '0' in
 String.set s k '1'; 
 for i = 0 to p.bound do
   if Info.is_equal p.heap.(i).(k) then
		 String.set s i '1'; 
		 let color =  string_of_int (p.data.(i).d2) in
   let unique =  string_of_int (snd p.data.(i).d3) in
     let cut_color = if p.cut.(i) <> empty_attribute then string_of_int (p.cut.(i).d.d2) else "Emp" in
	   let cut_beta_color = if p.cut.(i) <> empty_attribute then string_of_int (Info.get_beta_d2 p.cut.(i).r1) else "EmpBetaColor" in
     let cut_r = if p.cut.(i) <> empty_attribute then string_of_int (Info.get_relation p.cut.(i).r1) else "EmpCut" in
		 Buffer.add_string key color;
     Buffer.add_string key cut_color;
	   Buffer.add_string key cut_beta_color;
   Buffer.add_string key cut_r;
   if !example_name = "HSYstack" || !example_name = "ElimMS" then Buffer.add_string key unique;
 done;
  
 Buffer.add_string key s;

 let i = r p k in
if i < (p.bound+1) then begin
 if Info.is_reach_one p.heap.(k).(i) then
   begin
     Buffer.add_string key "1";
  	 compute_signiture p i;
	 end
	else
	 if Info.is_reach_more p.heap.(k).(i) then
    begin
      let color = string_of_int (Info.get_beta_d2 p.heap.(k).(i)) in
      Buffer.add_string key "2";
      Buffer.add_string key color;
		 compute_signiture p i;	
		end
end;
end
  
  
  
let rec compute_signiture_elim p k = begin
 let s = String.make (p.bound+1) '0' in
 String.set s k '1'; 
 for i = 0 to p.bound do
   if Info.is_equal p.heap.(i).(k) then
		 String.set s i '1'; 
 done;
 Buffer.add_string key s;

 let i = r p k in
if i < (p.bound+1) then begin
 if Info.is_reach_one p.heap.(k).(i) then
   begin
     Buffer.add_string key "1";
  	 compute_signiture_elim p i;
	 end
	else
	 if Info.is_reach_more p.heap.(k).(i) then
    begin
      Buffer.add_string key "2";
		 compute_signiture_elim p i;	
		end
end;
end
let signature p = begin
	Buffer.clear key;
    let start = start_index p in
  compute_signiture p start;

  for i = 0 to p.gvar-1 do
    compute_signiture_prev p i;
  done;

   let start1 = start_elim_index p in
  if start1 < (p.bound + 1) then begin
	 Buffer.add_string key "elim";
     compute_signiture_elim p start1; (*HSY*)
  end;
   
      let ret = (Buffer.contents key) in
	Buffer.clear key;
	ret
end
		   
(* No need to clone *)
let init_thread vars p thi : t list = begin
  let th = p.threads.(thi) in
  assert( th.range = 0);
  p.vars <- vars;
  let count = Array.length vars in
  let newBound = p.bound+count in
  let cutout = th.lbound in (* lower bound *)  
  let h = Array.make_matrix (newBound+1) (newBound+1) Info.none in
  let s = Array.make (newBound+1) 15 in
  let d = Array.make (newBound+1) {d1 = 1; d2 = 1;d3 = (0,4)} in
	let cut = Array.make (newBound+1) {r1 = Info.none; d = {d1 = 15; d2 = 15; d3 = (0,4)}; } in
	let bvars = Array.make (Array.length(p.bool_vars)) 0 in
	for i=0 to p.gvar - 1 do 
	  d.(i) <-   p.data.(i);
	  s.(i) <-   p.scope.(i);
		cut.(i) <- p.cut.(i);
	 done;
  for i=0 to cutout - 1 do
    for j=0 to cutout - 1 do (* Copy the colors and globals *) h.(i).(j) <- p.heap.(i).(j); done;
    for j=cutout to p.bound do (* Taking care of the threads *) h.(i).(j+count) <- p.heap.(i).(j); done;
  done;
  
  for i=cutout to p.bound do
    for j=0 to cutout - 1 do h.(i+count).(j) <- p.heap.(i).(j); done;
    for j=cutout to p.bound do h.(i+count).(j+count) <- p.heap.(i).(j); done;
  done;
  		for i = p.gvar to newBound do
    h.(i).(i) <- Info.equal;
	 done;
  let trans = Array.make count "" in
  (* update the bounds of the thread *)
  th.range <- count;
  th.trans <- trans;
  p.bound <- newBound;
  p.heap <- h;
	p.scope <- s;
  p.data <- d;
	p.cut  <- cut;
	p.flag <- Alone;
	p.interf_flag <- Alone;
	p.ret <- alone_ret;
	p.interf_ret <- alone_ret;
	p.value_vars <- bvars;
  (* update the bounds of the other (physically after) threads *)
  for thj=thi+1 to p.nth-1 do
    let th' = p.threads.(thj) in
    th'.lbound <- th'.lbound + count;
  done; 
  [p]
end
 
  
(* No need to clone *)
let kill_thread (p:t) (thi:int) : t list = begin 
	let pp = clone p in
  let th = p.threads.(thi) in
  let vars = th.range in
  let newBound = p.bound - vars in
  let cutout = th.lbound in (* lower bound *)
  (* Removing the thread labels *)
	for i=cutout to cutout + vars-1 do _kill p i; done;
  
	let h = Array.make_matrix (newBound+1) (newBound+1) Info.none in
  (* Copying to the new heap. AFTER the label removing!! *)
  for i=0 to cutout - 1 do
    for j=0 to cutout - 1 do h.(i).(j) <- p.heap.(i).(j); done;
    for j=cutout to newBound do h.(i).(j) <- p.heap.(i).(j+vars); done;
  done;
  for i=cutout to newBound do
    for j=0 to cutout - 1 do h.(i).(j) <- p.heap.(i+vars).(j); done;
    for j=cutout to newBound do h.(i).(j) <- p.heap.(i+vars).(j+vars); done;
  done;
  p.bound <- newBound;
	p.vars <- [||];
  p.heap <- h;
	p.value_vars <- Array.make (Array.length(p.bool_vars)) 0;
	p.flag <- Alone;
	p.interf_flag <- Alone;
	p.x_red <- true;
  p.ret <- alone_ret;
	p.interf_ret <- alone_ret;
  (* reset the thread *)
  th.pc      <- 0;
  th.return  <- Data.top;
  th.range   <- 0;
  th.trans   <- [||];
  (* update the bounds of the other (physically after) threads *)
  for thj=thi+1 to p.nth-1 do
    let th' = p.threads.(thj) in
    th'.lbound <- th'.lbound - vars;
  done;
  (*Kill uquire  *)
  for i = 1110 to p.bound do
    p.data.(i) <- {d1 = p.data.(i).d1; d2 = p.data.(i).d2; d3 = (0, snd p.data.(i).d3)};
  done; 
  [p]
end


(*The function is to get the next cutpoint of the variable or cutpoin at k position*)
let get_leaf p k = begin
  let ret = ref (p.bound+1) in
  for i = 0 to 2 do
	if Info.is_equal p.heap.(k).(i) then
		ret := i;
	done;
  !ret
end

(*index of variable of thi(fist or second) matrix in intersection matrix*)				
let new_index p1 i thi =
	(*first matrix*)
	if thi == 1 then i
	else (*second matrix*)	
	 begin
	   if i >= p1.gvar then i + (Array.length p1.vars) else i
end	

let pure_strengthen p = begin 
	 for i=0 to p.bound do
		for j=0 to p.bound do
		(*For each pair of equality matrixes*)	
    if (Info.is_equal p.heap.(i).(j)) && i <> j then 
      begin					       
			let merge_d = {d1 = p.data.(i).d1 land p.data.(j).d1; d2 = p.data.(i).d2(* land p.data.(j).d2*);d3 = p.data.(i).d3} in
			p.data.(i) <- 	merge_d;
			p.data.(j) <- 	merge_d;			
			 for k=0 to p.bound do
				  if (Info.is_none_no_ord p.heap.(k).(i)) then
				    p.heap.(k).(i) <- p.heap.(k).(j);
          if (Info.is_none_no_ord p.heap.(i).(k)) then	
					  p.heap.(i).(k) <- p.heap.(j).(k); 					
       done;
		end;	
	done;	
	done;
end

let compare_cells_set s1 s2  = begin
  let ret = ref true in
	for i = 0 to Array.length s1 - 1 do
		let elt = s1.(i) in
		let less_than = ref false in
		for j  = 0 to Array.length s2 - 1 do
			if Info.compare_cell elt s2.(j) then
				less_than := true;
		done;
		if not !less_than then ret := false; 
	done;
	!ret
end

let merge_cut cut1 cut2 = begin
	if cut1 = empty_attribute && cut2 = empty_attribute then
		cut1,true
	else
	if (cut1 = empty_attribute && cut2 <> empty_attribute) ||  (cut1 <> empty_attribute && cut2 = empty_attribute) then
		cut1,false
	else begin
    let merge_r1,res = Info.merge_cell cut1.r1 cut2.r1 in
		if res then begin
		   let merge_d = {d1 = cut1.d.d1 land cut2.d.d1; d2 = cut1.d.d2 land cut2.d.d2; d3 = (fst cut2.d.d3, snd cut1.d.d3 land snd cut2.d.d3);} in
           if cut1.d.d2 <> cut2.d.d2 then
					cut1, false
		   else
				{r1 = merge_r1; d = merge_d},true
		end
		else
			cut1,false
	end
end 

let compare_cut cut1 cut2 = begin
	if cut1 = empty_attribute && cut2 = empty_attribute then
		true
	else
	if (cut1 = empty_attribute && cut2 <> empty_attribute) ||  (cut1 <> empty_attribute && cut2 = empty_attribute) then
		false
	else begin
      if not (Info.compare_cell cut1.r1 cut2.r1) then false
	  else
	  if cut1.d.d1 land cut2.d.d1 = 0 || cut1.d.d2 land cut2.d.d2 = 0 || snd cut1.d.d3 land snd cut2.d.d3 = 0 then false
	  else true			   
	end
end

(*We only merge if two constraits have same signiture*)

let merge_constraint p1 p2 = begin
	let p = clone p1 in
  if p1.observer <> p2.observer || p1.value_vars <> p2.value_vars || p1.flag <> p2.flag || p1.ret.cnt <> p2.ret.cnt || p1.ret.add <> p2.ret.add || p1.ret.rmv <> p2.ret.rmv then
		p,false 
	else
	begin	
	  let res = ref true in
	  for i = 0 to p1.bound do
			let new_d1, new_d2,new_d3 = p1.data.(i).d1 lor p2.data.(i).d1, p1.data.(i).d2,(fst p2.data.(i).d3, snd p1.data.(i).d3 lor snd p2.data.(i).d3)  in
     if p1.data.(i).d2 <> p2.data.(i).d2 || fst p1.data.(i).d3 <> fst p2.data.(i).d3 then (*We dont merge when colors are different*)
				res := false
			else begin
			p.data.(i) <- {d1 = new_d1; d2 = new_d2; d3 = new_d3};	 
		  let merge_cut', ok = merge_cut p1.cut.(i) p2.cut.(i) in
		  if ok then p.cut.(i) <- merge_cut'
		  else
			  res := false;
		  for j = 0 to p2.bound do
			  let merge_cell, m = Info.merge_cell p1.heap.(i).(j) p2.heap.(i).(j) in
			  p.heap.(i).(j) <- merge_cell;
			  if not m then res := false;			
		  done;
			end;
	  done;
   if p.threads.(0).pc = 42224 && p.data.(8).d2 = 2  then begin print_cons p1; print_cons p2; print_string "ket qua"; print_cons p; end;
	p,!res
	end;
end

let assign_constraint p newp = begin
p.heap <- newp.heap;
p.data <- newp.data;
p.scope <- newp.scope;
p.cut <- newp.cut;
end

let compare_constraint p1 p2 = begin
 try
    if p1.observer <> p2.observer || (*HSY*)(*(p1.helper <> p2.helper && p1.threads.(0).pc = 23) ||*) (p1.value_vars <> p2.value_vars) || p1.threads.(0).pc <> p2.threads.(0).pc || (p1.flag <> p2.flag || p1.ret.cnt <> p2.ret.cnt || p1.ret.add <> p2.ret.add || p1.ret.rmv <> p2.ret.rmv )  then
			raise (EndLoopWithResult 31);
    for i = 0 to p1.bound do		
    if p1.data.(i).d1 land p2.data.(i).d1 <> p1.data.(i).d1 then raise (EndLoopWithResult 31);
		if p2.data.(i).d2 <> p1.data.(i).d2 then  raise (EndLoopWithResult 31);
    if not (compare_cut p1.cut.(i) p2.cut.(i))  then  raise (EndLoopWithResult 31); 
		for j = 0 to p1.bound do
			if not (Info.compare_cell p1.heap.(i).(j) p2.heap.(i).(j)) (*&& Info.is_reach p1.heap.(i).(j)*) then
				raise (EndLoopWithResult 31);
		done;
	done;	
	raise (EndLoopWithNothing 31);
	with 
  | (EndLoopWithResult 31) ->  false
	| (EndLoopWithNothing 31) ->  true
end
  

(*The fist case of matching two path when doing insersection*)
(* r(i1,i2) = r(r(i1), r(i2)) *)
let match_1 p1 p2 i1 i2 i3 = begin
	let empty_ret =  ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0), false	in 
  let next1,next2 =   Hashtbl.find p1.successor i1, Hashtbl.find p2.successor i2  in	
  (*dont mark the guy with already mark for book set*)  
	if (!example_name = "HMset" ) &&  p1.threads.(0).pc = 22 && (next1 = 6) && p2.data.(next2).d1 = 3  then  ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0), false	
	else 
  (*T harris set*)  
	if (!example_name = "THarris") && p1.threads.(0).pc = 36 && (next1 = 9) && p2.data.(next2).d1 = 3  then  ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0), false		
	else 
   	
	(*Martin Vechev*)
	if !example_name = "Vechev" && p1.threads.(0).pc = 22 && (next1 = 6) && p2.data.(next2).d1 = 3  then  ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0), false			
	else 
   if (fst p1.data.(next1).d3 = 1 && fst p2.data.(next2).d3 = 1) then begin  ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0), false end
     else
       
       if !example_name = "Unordered" && (p1.threads.(0).pc = 180 || p1.threads.(0).pc = 70) && next1 = 7 && p1.cut.(next1) <> empty_attribute && p2.cut.(next2) = empty_attribute  then  empty_ret
    else 
      
      if !example_name = "Unordered" && p1.threads.(0).pc = 31 && next1 = 8 && p2.data.(next2).d1 land 16 = 16 then
			empty_ret
		 else
     if !example_name = "Unordered" && p1.threads.(0).pc = 30 && next1 = 8 && p2.data.(next2).d1 land 8 = 8 then
			empty_ret
		 else

     if !example_name = "Unordered" && p1.threads.(0).pc = 58 && next1 = 6 && p2.data.(next2).d1 land 16 = 16 then
			empty_ret
		 else
     if !example_name = "Unordered" && p1.threads.(0).pc = 56 && next1 = 6 && p2.data.(next2).d1 land 4 = 4 then
			empty_ret
		 else
     if !example_name = "Unordered" && p1.threads.(0).pc = 18 && next1 = 5 && p1.cut.(next1) <> empty_attribute && p2.cut.(next2) = empty_attribute then
			empty_ret		
    else
	begin
	 let cell1, cell2 = p1.heap.(i1).(next1), p2.heap.(i2).(next2) in
	 let r1,r2 = Info.get_relation cell1, Info.get_relation cell2 in
	 if (next1 < p1.gvar || next2 < p2.gvar) && next1 <> next2 then
		 empty_ret	
	 else
	 if r1  = r2  then begin 
		 if r1 = 1 then begin						
		   let alpha =   Info.intersect_alpha cell1 cell2 in	
     let d1,d2,d3 = p1.data.(next1).d1 land p2.data.(next2).d1, p1.data.(next1).d2 land p2.data.(next2).d2, (fst p2.data.(next2).d3, (snd p1.data.(next1).d3) land  (snd p2.data.(next2).d3)) in	
		   let beta =    Info.get_beta cell1 in 
		   let r    =    r1 in	
     let ret = ((next1,next2), (r, alpha, beta, d1, d2, d3), next1) in
     if alpha = Info.zero_alpha || d1 = 0 || d2 = 0 || snd d3 = 0 then 
				 ret, false 
			 else
				 ret, true
			end				
		 else	
     if r1 = 2 then begin	
		   let alpha =   Info.intersect_alpha cell1 cell2 in	
       let d1,d2,d3 = p1.data.(next1).d1 land p2.data.(next2).d1, p1.data.(next1).d2 land p2.data.(next2).d2, ( fst p2.data.(next2).d3, (snd p1.data.(next1).d3) land  (snd p2.data.(next2).d3)) in		
		   let beta =    Info.intersect_beta cell1 cell2 in
		   let r    =    r1 in	
       let ret = ((next1,next2), (r, alpha, beta,d1,d2,d3), next1) in
       
       if alpha = Info.zero_alpha || beta = Info.emp_beta || d1 = 0 || d2 = 0 || snd d3 = 0 then 
				ret, false
			 else
				ret, true
			end
			else
				empty_ret	end												
		else
			empty_ret
	end
end
  

(*The second case of matching two path when doing insersection*)
(* r(i1,i2) = r(r(i1), i2) *)
let match_2 p1 p2 i1 i2 i3 = begin		    
	  let empty_ret = ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0), false, 0, 0, false	in
		let next1,next2, next2' = Hashtbl.find p1.successor i1, i2, Hashtbl.find p2.successor i2 in
		(*Lock free Hindsignt with observer*)
		if !example_name = "Vechev" && p1.threads.(0).pc = 17 && p1.observer <> Init && (next1 = 6 || next1 = 5)  then  ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0), false, 0, 0, false
		else
		if !example_name = "Vechev" && p1.threads.(0).pc = 22 && (next1 = 6) && p1.data.(next1).d2 <> 2  then  ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0), false, 0, 0, false
		else	
		(*MICHAEL AND BOOK*)		
		if (!example_name = "HMset") && p1.threads.(0).pc = 20 && p1.observer <> Init && (next1 = 6 || next1 = 5)  then   empty_ret
		else
			

    if !example_name = "Unordered" && p1.threads.(0).pc = 31 && next1 = 8 && Info.get_beta_d1 p2.heap.(i2).(next2') land 16 = 16 then
			empty_ret
		 else
     if !example_name = "Unordered" && p1.threads.(0).pc = 30 && next1 = 8 && Info.get_beta_d1 p2.heap.(i2).(next2') land 8 = 8 then
			empty_ret
       else
         if !example_name = "Unordered" && p1.threads.(0).pc = 18 && next1 = 5 && p1.cut.(next1) <> empty_attribute then
			empty_ret
		 else   

	  begin
	   let cell1, cell2 = p1.heap.(i1).(next1), p2.heap.(i2).(next2') in
		 let r1,r2 = Info.get_relation cell1, Info.get_relation cell2 in			
		 if next1 < p1.gvar then
        empty_ret
	   else	
		 if r2 == 2 then begin
		 let old_d1, old_d2, old_d3 = p1.data.(next1).d1, p1.data.(next1).d2, p1.data.(next1).d3 in 
		   (*alpha in p1 and beta in p2*)
			 if r1 = 1 then begin
				  let alpha, d1, d2, d3, next_color, split, cond =   Info.intersect_alpha_beta 1 cell1 cell2 old_d1 old_d2 old_d3 in	
		      let beta =    Info.get_beta cell1 in 
		      let r    =    r1 in	
      let ret = ((next1,next2), (r, alpha, beta, d1, d2,d3), next1) in
        if alpha = Info.zero_alpha || d1 = 0 || d2 = 0 || snd d3 = 0 then 
             empty_ret
			    else
             ret, true, next_color, split, cond
			    end
			 else
			 (*beta+alpha in p1 and beta in p2*)	
			 if r1 = 2 then begin
			(*First step is to intersect two beta first to get the first part intersected*)	
      let beta, next_beta_cell_color, s =    Info.intersect_beta' 1 cell1 cell2 in	
			 if  beta = Info.emp_beta then
				empty_ret
			 else 
				begin
					let cell2' = Info.assign_color cell2 next_beta_cell_color in
      let alpha, d1, d2, d3, next_color, split, cond =  Info.intersect_alpha_beta 1 cell1 cell2' old_d1 old_d2 old_d3 in						 
		      let r    =    r1 in	
      let ret = ((next1,next2), (r, alpha, beta, d1, d2, d3), next1) in
      
			    if alpha = Info.zero_alpha || d1 = 0 || d2 = 0  || snd d3 = 0 then 
            empty_ret
			    else
            ret, true, next_color, s, cond
			 end 
			end
			else
				  empty_ret
		 end
		 else
  empty_ret
	end
end

(*The third case of matching two path when doing insersection*)
(* r(i1,i2) = r(i1, r(i2)) *)
let match_3 p1 p2 i1 i2 i3 = begin
	  let empty_ret = ((0,0), (0, Info.emp_alpha, Info.emp_beta, 0,0,(0,0)), 0),false, 0, 0, false in
	  let next1,next2, next1' = i1, Hashtbl.find p2.successor i2, Hashtbl.find p1.successor i1 in	
	  let cell1, cell2 = p1.heap.(i1).(next1'), p2.heap.(i2).(next2) in
  	let r1,r2 = Info.get_relation cell1, Info.get_relation cell2 in
		if next2 < p2.gvar then
     empty_ret		
	  else			
    if r1 == 2  then begin 
			let old_d1, old_d2, old_d3 = p2.data.(next2).d1,p2.data.(next2).d2,p2.data.(next2).d3  in 
			 if r2 = 1 then begin
				  let alpha, d1, d2,d3, next_color, split, cond = Info.intersect_alpha_beta 2 cell2 cell1 old_d1 old_d2 old_d3 in		
					let beta =    Info.get_beta cell2 in 
		      let r    =    r2 in	
      let ret = ((next1,next2), (r, alpha, beta, d1, d2, d3), next2) in	
       if alpha = Info.zero_alpha || d1 = 0 || d2 = 0 || snd d3 = 0 then 
            empty_ret
			    else
            ret, true, next_color, split, cond
			    end
			 else
			 if r2 = 2 then begin
      let beta, next_beta_cell_color, s =    Info.intersect_beta' 2 cell1 cell2 in	
			  if beta = Info.emp_beta then
				  empty_ret
			  else 
				begin
					let cell1' = Info.assign_color cell1 next_beta_cell_color in
      let alpha,d1,d2,d3, next_color, split, cond =  Info.intersect_alpha_beta 2 cell2 cell1' old_d1 old_d2 old_d3 in		
		      let r    =  r2 in	
      let ret = ((next1,next2), (r, alpha, beta, d1, d2, d3), next2) in
      
			    if alpha = Info.zero_alpha || d1 = 0 || d2 = 0 || snd d3 = 0 then 
            empty_ret
			    else
            ret, true, next_color, s, cond
			 end
			end
			 else
				  empty_ret	
		end
		 else
       empty_ret
end
 
  
  
(*The fist case of matching two path when doing insersection*)
(* r(i1,i2) = r(r(i1), r(i2)) *)
let match_1_elim p1 p2 i1 i2 i3 = begin
	let empty_ret =  ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0), false	in 
  let next1,next2 =   Hashtbl.find p1.successor i1, Hashtbl.find p2.successor i2  in	
	if !example_name = "ElimMS" && p1.threads.(0).pc = 42 && (next1 = 6) && p2.data.(next2).d1 = 3  then empty_ret
  else
	if !example_name = "HSYstack1" && p1.threads.(0).pc = 9 && (next1 = 6) && p2.data.(next2).d1 = 3  then empty_ret
  else
  if !example_name = "HSYstack1" && p1.threads.(0).pc = 51 && (next1 = 6) && p2.data.(next2).d1 = 3  then empty_ret
  else	
  if !example_name = "HSYstack1" && p1.threads.(0).pc = 11 && (next1 = 7) && p2.data.(next2).d1 = 3  then empty_ret
  else
  if !example_name = "HSYstack1" && p1.threads.(0).pc = 54 && (next1 = 7) && p2.data.(next2).d1 = 3  then empty_ret
  else					
	(*two pid can not be matched*)  
	begin
	 let cell1, cell2 = p1.heap.(i1).(next1), p2.heap.(i2).(next2) in
	 let r1,r2 = Info.get_relation cell1, Info.get_relation cell2 in
	 if (next1 < p1.gvar || next2 < p2.gvar) && next1 <> next2 then
		  begin
    
          empty_ret
            end	
	 else
	 if r1  = r2  then begin 
		 if r1 = 1 then begin						
		   let alpha =   Info.intersect_alpha cell1 cell2 in	
			 let d1,d2,d3 = p1.data.(next1).d1 land p2.data.(next2).d1, p1.data.(next1).d2 land p2.data.(next2).d2, (0, (snd p1.data.(next1).d3) land (snd p2.data.(next2).d3)) in	
		   let beta =    Info.get_beta cell1 in 
		   let r    =    r1 in	
			 let ret = ((next1,next2), (r, alpha, beta, d1, d2, d3), next1) in
       if alpha = Info.zero_alpha || d1 = 0 || d2 = 0 || snd d3 = 1230 then 
				 ret, false 
			 else
				 ret, true
			end				
		 else	
     if r1 = 2 then begin	
		   let alpha =   Info.intersect_alpha cell1 cell2 in	
		   let d1,d2,d3 = p1.data.(next1).d1 land p2.data.(next2).d1, p1.data.(next1).d2 land p2.data.(next2).d2, (0, (snd p1.data.(next1).d3) land (snd p2.data.(next2).d3)) in		
		   let beta =    Info.intersect_beta_elim cell1 cell2 in
		   let r    =    r1 in	
		   let ret = ((next1,next2), (r, alpha, beta,d1,d2,d3), next1) in
       if alpha = Info.zero_alpha || beta = Info.emp_beta || d1 = 0 || d2 = 0 || snd d3 = 1230 then 
				ret, false
			 else
				ret, true
			end
			else
				 begin
       
          empty_ret
            end	end												
		else
			 begin
         empty_ret
            end
	end
end

(*The second case of matching two path when doing insersection*)
(* r(i1,i2) = r(r(i1), i2) *)
let match_2_elim p1 p2 i1 i2 i3 = begin		    
	  let empty_ret = ((0,0), (0, Info.emp_alpha, Info.emp_beta,0,0,(0,0)), 0),false	in
		let next1,next2, next2' = Hashtbl.find p1.successor i1, i2, Hashtbl.find p2.successor i2 in
		if !example_name = "ElimMS" && p1.threads.(0).pc = 42 && (next1 = 6) && (snd (Info.get_beta_d3 p2.heap.(i2).(next2'))) = 3 then empty_ret
    else
	  if !example_name = "HSYstack1" && p1.threads.(0).pc = 9 && (next1 = 6) && (snd (Info.get_beta_d3 p2.heap.(i2).(next2'))) = 3 then empty_ret
    else
    if !example_name = "HSYstack1" && p1.threads.(0).pc = 51 &&(next1 = 6) && (snd (Info.get_beta_d3 p2.heap.(i2).(next2'))) = 3  then empty_ret
    else	
    if !example_name = "HSYstack1" && p1.threads.(0).pc = 11 &&(next1 = 6) && (snd (Info.get_beta_d3 p2.heap.(i2).(next2'))) = 3  then empty_ret
    else
    if !example_name = "HSYstack1" && p1.threads.(0).pc = 54 && (next1 = 6) && (snd (Info.get_beta_d3 p2.heap.(i2).(next2'))) = 3  then empty_ret
    else						
		(*Lock free Hindsignt with observer*)	  	 
		begin
	   let cell1, cell2 = p1.heap.(i1).(next1), p2.heap.(i2).(next2') in
		 let r1,r2 = Info.get_relation cell1, Info.get_relation cell2 in			
		 if next1 < p1.gvar then
        empty_ret
	   else	
		 if r2 == 2 then begin
		 let old_d1, old_d2, old_d3 = p1.data.(next1).d1, p1.data.(next1).d2, p1.data.(next1).d3 in 
		   (*alpha in p1 and beta in p2*)
			 if r1 = 1 then begin
				  let alpha, d1, d2, d3 =   Info.intersect_alpha_beta_elim cell1 cell2 old_d1 old_d2 old_d3 in	
		      let beta =    Info.get_beta cell1 in 
		      let r    =    r1 in	
			    let ret = ((next1,next2), (r, alpha, beta, d1, d2,d3), next1) in
      if alpha = Info.zero_alpha || d1 = 0 || d2 = 0 || snd d3 = 1230 then begin 
        empty_ret end
			    else
             ret, true
			    end
			 else
			 (*beta+alpha in p1 and beta in p2*)	
			 if r1 = 2 then begin
			(*First step is to intersect two beta first to get the first part intersected*)	
			 let beta =    Info.intersect_beta_elim cell1 cell2 in	
      if  beta = Info.emp_beta then
        begin
              empty_ret
            end
			 else 
				begin
					let alpha, d1, d2, d3 =  Info.intersect_alpha_beta_elim cell1 cell2 old_d1 old_d2 old_d3 in						 
		      let r    =    r1 in	
			    let ret = ((next1,next2), (r, alpha, beta, d1, d2, d3), next1) in
			    if alpha = Info.zero_alpha || d1 = 0 || d2 = 0  || snd d3 = 1230 then 
            begin
                 empty_ret
            end
			    else
            ret, true
			 end 
			end
			else
				  begin
                 empty_ret
            end
		 end
		 else
  empty_ret
	end
end

(*The third case of matching two path when doing insersection*)
(* r(i1,i2) = r(i1, r(i2)) *)
let match_3_elim p1 p2 i1 i2 i3 = begin
	  let empty_ret = ((0,0), (0, Info.emp_alpha, Info.emp_beta, 0,0,(0,0)), 0),false in
	  let next1,next2, next1' = i1, Hashtbl.find p2.successor i2, Hashtbl.find p1.successor i1 in	
	  let cell1, cell2 = p1.heap.(i1).(next1'), p2.heap.(i2).(next2) in
  	let r1,r2 = Info.get_relation cell1, Info.get_relation cell2 in
		if next2 < p2.gvar then
    begin
           empty_ret
            end	
	  else			
    if r1 == 2  then begin 
			let old_d1, old_d2, old_d3 = p2.data.(next2).d1,p2.data.(next2).d2,p2.data.(next2).d3  in 
			 if r2 = 1 then begin
				  let alpha, d1, d2,d3 = Info.intersect_alpha_beta_elim cell2 cell1 old_d1 old_d2 old_d3 in		
					let beta =    Info.get_beta cell2 in 
		      let r    =    r2 in	
			    let ret = ((next1,next2), (r, alpha, beta, d1, d2, d3), next2) in					
			    if alpha = Info.zero_alpha || d1 = 0 || d2 = 0 || snd d3 = 1230 then 
             begin
                             
          empty_ret
            end
			    else
            ret, true
			    end
			 else
			 if r2 = 2 then begin
				let beta =    Info.intersect_beta_elim cell1 cell2 in	
			  if beta = Info.emp_beta then
				  empty_ret
			  else 
				begin
				  let alpha,d1,d2,d3  =  Info.intersect_alpha_beta_elim cell2 cell1 old_d1 old_d2 old_d3 in		
		      let r    =  r2 in	
			    let ret = ((next1,next2), (r, alpha, beta, d1, d2, d3), next2) in
			    if alpha = Info.zero_alpha || d1 = 0 || d2 = 0 || snd d3 = 1230 then 
            begin
                             
          empty_ret
            end
			    else
            ret, true
			 end
			end
			 else
				  empty_ret	
		end
		 else
       empty_ret
end
let rec ord_two_cells p x y = begin
	let next = r p x in
	if not (is_leaf p next) then 
		begin
	    let cell = p.heap.(x).(next) in
	    if Info.get_relation cell = 2 then 
				if next <> y then
		     (Info.get_beta_ord cell land Info.get_alpha_ord cell) land ord_two_cells p next y
				else
				 (Info.get_beta_ord cell land Info.get_alpha_ord cell)
	    else if Info.get_relation cell = 1 then 
				if next <> y then
	       (Info.get_alpha_ord cell) land ord_two_cells p next y
				else
					(Info.get_alpha_ord cell)
			else
				7
	end 
	else
		7
end	
(*Invert the lock*)
let invert_lock_constraint p = begin
let p' = clone p in
for i = 0 to p'.bound do
	if p'.scope.(i) == 1 then p'.data.(i) <- {d1 = p'.data.(i).d1; d2 = p'.data.(i).d2; d3 = if snd p'.data.(i).d3 = 1 then (0, 2) 
	   else if snd p'.data.(i).d3 = 4 then (0, 4) else (0, fst p'.data.(i).d3)};
	for j = 0 to p'.bound do
		if Info.is_reach p'.heap.(i).(j) && p'.scope.(i) == 1 then
			p'.heap.(i).(j) <- Info.invert_cell_lock p'.heap.(i).(j);
	done
done;
p'
end

(*//////////////////////////////////////////////////////////////////Abstract Away//////////////////////////////////////////////////////////////////*)
let abstract_away p fro til p2 = begin		
   for i = fro+1 to til do
    _mergeover p i fro til;
	 done; 
   let newbound = p2.bound in
	 (*the matrix after abstracting will be same as p1 in structure*)
  let newp = clone p2 in
  newp.ret <-p2.ret;
  newp.x_red <- p2.x_red;
	 let newheap =  Array.make_matrix (newbound+1) (newbound+1) Info.none in	
	 let newscope = Array.make (newbound+1) 15 in
   let newsdata = Array.make (newbound+1) {d1 = 1; d2 = 1; d3 = (0,4)} in
	 let newcut = Array.make (newbound+1) {r1 = Info.none; d = {d1 = 15; d2 = 15;d3 = (0,4)};} in
	 (*Update scope  of variables*)	
	 for i = 0 to p.bound do
		   if i <= fro then begin
         newscope.(i) <- p.scope.(i);
			   newsdata.(i) <- p.data.(i);
			   newcut.(i)   <- p.cut.(i);
			 end
			 else
			 if i > til then
       begin
				 newscope.(i-(til - fro)) <- p.scope.(i);
			   newsdata.(i-(til - fro)) <- p.data.(i); 
				 newcut.(i-(til - fro)) <- p.cut.(i); 
			 end
	 done;
	 newp.bound <- newbound;
	 newp.heap <- newheap;
	 newp.scope <- newscope;
	 newp.data <- newsdata;
	 newp.cut  <- newcut;
  (*Update matrix*)
  for i = 0 to p.bound do
    for j = 0 to p.bound do
		if i <= fro then 
		 begin
		  if j <= fro then
      newp.heap.(i).(j) <- p.heap.(i).(j)
		  else
			 if j > til then
         newp.heap.(i).(j - (til - fro)) <- p.heap.(i).(j)
		 end
		else
		 if i > til then 
			begin
		   if j <= fro then
       newp.heap.(i- (til - fro)).(j) <- p.heap.(i).(j)
		   else
			  if j > til then
       newp.heap.(i- (til - fro)).(j - (til - fro)) <- p.heap.(i).(j)
		  end
    done;
  done;
	   newp.threads.(0).pc <- p.threads.(0).interf_pc;
		newp.observer <- p.observer;
  newp.events <- p.events;	
 
	if p.interf_flag = Interf then
		begin		
			newp.flag <- p.interf_flag;
			p.interf_flag <- Alone;
			newp.interf_flag <- Alone;
	end;
	
		if p.interf_ret <> alone_ret then
		begin		
			newp.ret <- p.interf_ret;
			p.interf_ret <- alone_ret;
			newp.interf_ret <- alone_ret;
	end;
  
  newp
end
  
  
  
(*//////////////////////////////////////////////////////////////////Abstract Away//////////////////////////////////////////////////////////////////*)
let abstract_away_p2 p fro til p1 = begin		
  for i = p1.bound+1 to p.bound do
    _mergeover p i (p1.bound+1) p.bound;
	 done;
   let newbound = p1.bound in
	 (*the matrix after abstracting will be same as p1 in structure*)
   let newp = clone p1 in
	 let newheap =  Array.make_matrix (newbound+1) (newbound+1) Info.none in	
	 let newscope = Array.make (newbound+1) 15 in
   let newsdata = Array.make (newbound+1) {d1 = 1; d2 = 1; d3 = (0,4)} in
	 let newcut = Array.make (newbound+1) {r1 = Info.none; d = {d1 = 15; d2 = 15;d3 = (0,4)};} in
	 (*Update scope  of variables*)	
	 for i = 0 to p1.bound do
		newscope.(i) <- p.scope.(i);
        newsdata.(i) <- p.data.(i);
	    newcut.(i)   <- p.cut.(i);
	 done;
	 newp.bound <- newbound;
	 newp.heap <- newheap;
	 newp.scope <- newscope;
	 newp.data <- newsdata;
	 newp.cut  <- newcut;
  (*Update matrix*)
  for i = 0 to p1.bound do
    for j = 0 to p1.bound do
      newp.heap.(i).(j) <- p.heap.(i).(j)
    done;	  
  done;
  newp.observer <- p.observer;
	newp.events <- p.events;
  newp
end
(*Extend the two configurations into one*)

let extend p1 p2 = begin
 (*
  update_scope p1;
  update_scope p2;
  *)
	let bound = p1.bound + (Array.length p2.vars) in
	let h = Array.make_matrix (bound+1) (bound+1) Info.none in
	let p = clone p1 in
	for i = 0 to bound do
		h.(i).(i) <- Info.equal;
		for j = 0 to bound do
    if i <= p1.bound && j <= p1.bound  then  
      if Info.is_none_ord p1.heap.(i).(j) || Info.is_equal p1.heap.(i).(j) || p1.scope.(i) == 3 then
						 h.(i).(j) <-  p1.heap.(i).(j);	
     if i > p1.bound && j > p1.bound then 
				  if Info.is_none_ord p2.heap.(i-Array.length p1.vars).(j-Array.length p1.vars) ||
					Info.is_equal p2.heap.(i-Array.length p1.vars).(j-Array.length p1.vars) || p2.scope.(i-Array.length p1.vars) = 3 then 
						h.(i).(j) <-  p2.heap.(i-Array.length p1.vars ).(j-Array.length p1.vars);		
			if i > p1.bound && j < p1.gvar then
     if Info.is_none_ord p2.heap.(i-Array.length p1.vars).(j) || Info.is_equal p2.heap.(i-Array.length p1.vars).(j) || p2.scope.(i-Array.length p1.vars) = 3 || (Info.is_reach p2.heap.(i-Array.length p1.vars).(j) && j = 2)  then
						 h.(i).(j) <-  p2.heap.(i-Array.length p1.vars).(j);				
			if i < p1.gvar && j > p1.bound then
				 if Info.is_none_ord p2.heap.(i).(j-Array.length p1.vars) || Info.is_equal p2.heap.(i).(j-Array.length p1.vars) || p2.scope.(i) = 3 then
					   h.(i).(j) <-  p2.heap.(i).(j-Array.length p1.vars);									
	  done;
	done;
	p.heap  <- h;
	p.bound <- bound;
	p.vars  <- Array.append p1.vars p2.vars;
	p.translation = p1.translation;
	(*Extend the scope of variables of the two configurations*)
	let scope = Array.make (bound+1) 15 in
	let data =  Array.make (bound+1) {d1 = 1; d2 = 1; d3 = (0,4)} in
	let cut  =  Array.make (bound+1) {r1 = Info.none; d = {d1= 15; d2 = 15;d3 = (0,4)};} in
  for i = 0 to bound do
	   if i <= p1.bound  then 
			begin
	     scope.(i) <- p1.scope.(i); 
			 data.(i)  <- p1.data.(i);
			 cut.(i)   <- p1.cut.(i); 
	   end
	  else 
		 begin
		  scope.(i) <- p2.scope.(i - (Array.length p1.vars));
			data.(i)  <- p2.data.(i -  (Array.length p1.vars));
			cut.(i)   <- p2.cut.(i -   (Array.length p1.vars)); 
		 end;
	done;
	p.scope <- scope;
	p.data  <- data;
	p.cut   <- cut;
	(*update intersection pc to pc of p2, it will be used as pc after abstraction away*)
	p.threads.(0).interf_pc <- p2.threads.(0).pc; 
	p
end
 

let copy p p1 p2 = begin
	let c = extend p1 p2 in
	(*copy relation of new1 and new2*)
	for i = 0 to c.bound do
	   for j = 0 to c.bound do
			 if p.scope.(i) <> 3 && p.scope.(j) <> 3 then
				c.heap.(i).(j) <- p.heap.(i).(j);
		 done;
	done;
	c
end

let update_equal p i1 i2 = begin
let p1 = clone p in 
p1.heap.(i1).(i2) <- Info.equal;
p1.heap.(i2).(i1) <- Info.equal;
p1
end

let update_equal1 p new_d1 new_d2 new_d3 i1 i2 = begin
let p1 = clone p in 
p1.heap.(i1).(i2) <- Info.equal;
p1.heap.(i2).(i1) <- Info.equal;
p1.data.(i1) <- {d1 = new_d1; d2 = new_d2; d3 = new_d3}; 
p1.data.(i2) <- {d1 = new_d1; d2 = new_d2; d3 = new_d3}; 
p1
end

let update_cell p r new_alpha new_beta new_d1 new_d2 new_d3 i1 i2 = begin
   let p1 = clone p in
	 p1.heap.(i1).(i2) <- Info.create_cell r new_alpha new_beta;
	 p1.data.(i2) <- {d1 = new_d1; d2 = new_d2; d3 = new_d3}; 
	 p1
end

let elim p = p.threads.(0).pc == 400 && (Info.is_equal p.heap.(3).(8))
  
let check_global_lock_consistent p1 p2 = begin  
  let ret = ref true in
  for i = 3 to p1.gvar-1 do
    if Label.is_lock_global p1.gvars.(i-3) then
      if snd p1.data.(i).d3 = snd p2.data.(i).d3 && snd p1.data.(i).d3 = 1 then
        ret := false;
  done;
  !ret
end  

let rec intersection p p1 p2 i1 i2 i3 thi = begin
	if p1.observer <> p2.observer || p1.events <> p2.events then
		[p], false
	else
   if not (check_global_lock_consistent p1 p2) then
     [p], false
	else
	(*Both of states are leafs and equal*)	
  if is_leaf p1 i1 && is_leaf p2 i2 (*&& (get_leaf p1 i1) = (get_leaf p2 i2)*) then 
		begin
				p.heap.(i1).(new_index p1 i2 2) <- Info.equal;
		    [p],true
	  end
	  else 
      (*One of the state is leaf but the other one is not*)
	  if ((not (is_leaf p1 i1)) && (is_leaf p2 i2)) then
	   [],false
	  else
			if ((is_leaf p1 i1) && (not (is_leaf p2 i2))) then
	   [],false
	  else
       if i1 = i2 && (p1.data.(i1).d1 land p2.data.(i2).d1 == 0 || p1.data.(i1).d2 <> p2.data.(i2).d2) && i1 < p1.gvar then
       [], false
       else
	   (*T Harris*)
     if !example_name = "THarris1" && List.mem p2.threads.(0).pc [22;25] &&  (p2.cut.(9) <> empty_attribute ||  p2.data.(9).d1 = 2 || p2.data.(7).d1 = 2  || p2.cut.(7) <> empty_attribute)  then (*OK*)
			[], false
      else	         
   begin
   (*Otherwise we need to go down and check to see what happen*)
	  (*first match*)		
	  let inter1, res1 = begin
	  let mat_1 = match_1 p1 p2 i1 i2 i3 in 
	   match mat_1 with
     | _, false -> [],false 
		 | mat, true -> let (i1',i2'), (r, alpha, beta, d1, d2, d3), i3' = mat in				               																			
		                match intersection p p1 p2 i1' i2' i3' 1 with 
                    | _, false   -> [],false 
		                | newp, true -> let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> update_cell (update_equal1 hd d1 d2 d3 i1' (new_index p1 i2' 2)) r alpha beta d1 d2 d3 (new_index p1 i3 thi) i3'::update tl in
													(update newp), true					
											end in 
	  (*second match*)   
    let inter2, res2 = begin	
    let mat_2 = match_2 p1 p2 i1 i2 i3 in				
	   match mat_2 with
      | _, false, _,  _, _ ->  [],false 
		| mat, true, next_color, split, cond -> let (i1',i2'), (r, alpha, beta, d1, d2, d3), i3' = mat in	
		               let inter21,res21 = begin		
		               let p2' = clone p2 in 
									 p2'.heap.(i2).(Hashtbl.find p2.successor i2) <- Info.assign_color p2'.heap.(i2).(Hashtbl.find p2.successor i2)	next_color;								 
									 match intersection p p1 p2' i1' i2' i3' 1 with 
		               | _, false    -> [],false 
		               | newp, true  ->  let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> update_cell hd  r alpha beta d1 d2 d3 (new_index p1 i3 thi) i3'::update tl in
													(update newp), true 
									 end in
									
									 let inter22,res22 = if split = 0 then
										  [],false
									 else begin
									 let p2'' = clone p2 in p2''.heap.(i2).(Hashtbl.find p2.successor i2) <- Info.update_reach_one p2''.heap.(i2).(Hashtbl.find p2.successor i2); 
                   (*Depend on next color, the d1 will be updated, its only for the set*)
                   p2''.data.(i2') <- {d1 = if next_color = 32 then 2 else 1; d2 = next_color; d3 =  p2''.data.(i2').d3 };
                   if p2''.data.(i2').d2 == p1.data.(i1').d2 || (not cond) then begin												
		               match intersection p p1 p2'' i1' i2' i3' 1 with 
		               | _, false    -> [],false 
		               | newp, true  -> let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> update_cell hd  r alpha beta d1 d2 d3 (new_index p1 i3 thi) i3'::update tl in
													(update newp), true 
									end
									else
										[], false
									end in
    inter21 @ inter22, res21 || res22
								  
	  end in	
	  (*third match*) 
     let inter3, res3 = begin
      let mat_3 = match_3 p1 p2 i1 i2 i3 in
      
	   match mat_3 with
      | _, false, _, _,_ ->  [],false 
		 | mat, true, next_color, split, cond -> let (i1',i2'), (r, alpha, beta, d1, d2, d3), i3' = mat in
		               let inter31,res31 = begin	
									 let p1' = clone p1 in
			  					 p1'.heap.(i1).(Hashtbl.find p1.successor i1) <- Info.assign_color p1'.heap.(i1).(Hashtbl.find p1.successor i1) next_color;	
									 match intersection p p1' p2 i1' i2' i3' 2 with 
		               | _, false    -> [], false 
		               | newp, true  -> let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> update_cell hd r alpha beta d1 d2 d3 (new_index p1 i3 thi) (new_index p1 i3' 2)::update tl in
													(update newp), true	 
									 end in
									 
									 let inter32, res32 = if split = 0 then
									    [],false
									 else	begin
									 let p1'' = clone p1 in p1''.heap.(i1).(Hashtbl.find p1.successor i1) <- Info.update_reach_one p1''.heap.(i1).(Hashtbl.find p1.successor i1);
                   p1''.data.(i1') <- {d1 = if next_color = 32 then 2 else 1; d2 = next_color; d3 = p1''.data.(i1').d3};
                   if p1''.data.(i1').d2 == p2.data.(i2').d2 || (not cond) then begin
									 match intersection p p1'' p2 i1' i2' i3' 2 with 
		               | _, false    -> [], false 
		               | newp, true  -> let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> update_cell hd r alpha beta d1 d2 d3 (new_index p1 i3 thi) (new_index p1 i3' 2)::update tl in
													(update newp), true	
									end  
									else
										[], false
									 end in
									  inter31 @ inter32, res31 || res32
		end in	
	
    inter1@inter2@inter3, res1 || res2 || res3		
	end
end
 
  
  
 
  let is_full p =
	let r = ref 0 in
	for i = 6 to p.bound do
	  if Info.is_reach p.heap.(5).(i) then
			r := i;
	done;
	if Info.is_reach_more p.heap.(5).(!r) && (snd (Info.get_beta_d3 p.heap.(5).(!r))) land 16 <> 0 then true else false

let is_full' p =
	let r = ref 0 in
	for i = 6 to p.bound do
	  if Info.is_reach p.heap.(5).(i) then
			r := i;
	done;
	if Info.is_reach_more p.heap.(5).(!r) && (snd (Info.get_beta_d3 p.heap.(5).(!r))) land 8 <> 0 then true else false
 	
    
let rec intersection_elim p p1 p2 i1 i2 i3 thi = begin
 if p1.observer <> p2.observer || p1.events <> p2.events then
		[p], false
	else
	(*Both of states are leafs and equal*)	
  if is_leaf p1 i1 && is_leaf p2 i2 && (get_leaf p1 i1) = (get_leaf p2 i2) then 
		begin
				p.heap.(i1).(new_index p1 i2 2) <- Info.equal;
 	    [p],true
  end
    else
      if  p2.bound > 9 && Info.is_reach p2.heap.(9).(3) then
	   [],false
	  else 
		(*One of the state is leaf but the other one is not*)
     if ((not (is_leaf p1 i1)) && (is_leaf p2 i2)) then
       begin
         print_cons p1;print_cons p2;
         [],false
       end    
	  else
			if ((is_leaf p1 i1) && (not (is_leaf p2 i2))) then
	  begin
         print_cons p1;print_cons p2;
         [],false
       end    
	  else	  begin		
	  (*Otherwise we need to go down and check to see what happen*)
	  (*first match*)		
	  let inter1, res1 = begin
	  let mat_1 = match_1_elim p1 p2 i1 i2 i3 in 
	   match mat_1 with
     | _, false -> (*if Info.is_reach_more p1.heap.(4).(5) && p1.threads.(0).pc = 2 && p2.threads.(0).pc = 8 && i1 = 4 && i2 = 8 then begin print_int i1; print_string "--- "; print_int i2; print_string "first"; print_cons p1; print_string "second"; print_cons p2 end;*)[],false 
		 | mat, true -> let (i1',i2'), (r, alpha, beta, d1, d2, d3), i3' = mat in				               																			
     match intersection_elim p p1 p2 i1' i2' i3' 1 with 
                    | _, false   -> [],false 
		                | newp, true -> let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl ->  
              let newcell = update_cell (update_equal1 hd d1 d2 d3 i1' (new_index p1 i2' 2)) r alpha beta d1 d2 d3 (new_index p1 i3 thi) i3' in
                    newcell::update tl in
													(update newp), true					
											end in 
	  (*second match*)   
     let inter2, res2 = begin	
    let mat_2 = match_2_elim p1 p2 i1 i2 i3 in				
	   match mat_2 with
      | _, false ->  [],false 
      | mat, true -> 
        let (i1',i2'), (r, alpha, beta, d1, d2, d3), i3' = mat in	
                let inter21,res21 = begin
		               match intersection_elim p p1 p2 i1' i2' i3' 1 with 
		               | _, false    -> [],false 
		               | newp, true  ->  let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> 
                let newcell = update_cell hd  r alpha beta d1 d2 d3 (new_index p1 i3 thi) i3' in 
              newcell::update tl in
													(update newp), true 
							
        end in	
       let inter22,res22 = if Info.is_reach_one p2.heap.(i2).(Hashtbl.find p2.successor i2) then
										  [],false
									 else begin
									 let p2'' = clone p2 in p2''.heap.(i2).(Hashtbl.find p2.successor i2) <- Info.update_reach_one p2''.heap.(i2).(Hashtbl.find p2.successor i2); 
                   (*Depend on next color, the d1 will be updated, its only for the set*)
                  match intersection_elim p p1 p2'' i1' i2' i3' 1 with 
		               | _, false    -> [],false 
		               | newp, true  -> let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> update_cell hd  r alpha beta d1 d2 d3 (new_index p1 i3 thi) i3'::update tl in
													(update newp), true 
                   end in
       inter21 @ inter22, res21 || res22
     end in
	  (*third match*) 
    let inter3, res3 = begin
    let mat_3 = match_3_elim p1 p2 i1 i2 i3 in
	   match mat_3 with
      | _, false->  [],false 
      | mat, true -> let (i1',i2'), (r, alpha, beta, d1, d2, d3), i3' = mat in
        let inter31, res31 = begin
									 match intersection_elim p p1 p2 i1' i2' i3' 2 with 
		               | _, false    -> [], false 
		               | newp, true  -> let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> 
               let newcell = update_cell hd r alpha beta d1 d2 d3 (new_index p1 i3 thi) (new_index p1 i3' 2) in 
                newcell::update tl in
													(update newp), true	 										
    end in		
     let inter32, res32 = if Info.is_reach_one p1.heap.(i1).(Hashtbl.find p1.successor i1) then
									    [],false
									 else	begin
									 let p1'' = clone p1 in p1''.heap.(i1).(Hashtbl.find p1.successor i1) <- Info.update_reach_one p1''.heap.(i1).(Hashtbl.find p1.successor i1);
                      match intersection p p1'' p2 i1' i2' i3' 2 with 
		               | _, false    -> [], false 
		               | newp, true  -> let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> update_cell hd r alpha beta d1 d2 d3 (new_index p1 i3 thi) (new_index p1 i3' 2)::update tl in
													(update newp), true	
					end in 
        inter31 @ inter32, res31 || res32
    end in			
     inter1@inter2@inter3, res1 || res2 || res3		
	end
end
  

let do_intersection_elim p p1 p2  thi = begin  
  let start1 = start_elim_index p1 in
  let start2 = start_elim_index p2 in 
  if start1 = start2 && start1 = (p1.bound+1)  then
    [p],true
  else
  if start1 <> start2  then
    [],false
  else
    intersection_elim p p1 p2 start1 start2 start1 thi
  end
  
  
  let do_intersection p1 p2 i1 i2 i3 thi = begin  
  let p =	extend p1 p2 in	
		 p.interf_ret <- p2.ret;
     p.data.(3) <- {d1 = p1.data.(3).d1 land p2.data.(3).d1; d2 = p1.data.(3).d2 land p2.data.(3).d2; d3 =  (fst p2.data.(3).d3, (snd p1.data.(3).d3) land  (snd p2.data.(3).d3))};
       
	begin
	let ret = ref [] in
   let p',res =  do_intersection_elim p p1 p2 thi in
    
      if res then begin
   List.iter (fun x -> let t,res' = 
        
        if (p1.data.(3).d1 land p2.data.(3).d1 = 0 ||  p1.data.(3).d2 land p2.data.(3).d2 = 0 
      || ((snd p1.data.(3).d3) land (snd p2.data.(3).d3)) = 0)  || (fst p1.data.(3).d3 = 1 && fst p2.data.(3).d3 = 1) 
      then 
        [],false
      else 
        
        intersection x p1 p2 i1 i2 i3 thi in List.iter ( fun k -> if res' then begin ret := k::!ret end;) t) p';
    end;
      if List.length !ret > 0 then begin	
       !ret,true
        end
	else
	!ret, false
  end;

   end
   
  let do_intersection_CCAS p1 p2 i1 i2 i3 thi = begin
    let p =	extend p1 p2 in	
			for i = 0 to p.bound do
		p.heap.(i).(i) <- Info.equal;
		for j = 0 to p.bound do
			if i <= p1.bound && j <= p1.bound  then 
						 p.heap.(i).(j) <-  p1.heap.(i).(j);					
			if i > p1.bound && j > p1.bound then 
						p.heap.(i).(j) <-  p2.heap.(i-Array.length p1.vars ).(j-Array.length p1.vars);		
			if i > p1.bound && j < p1.gvar then
						 p.heap.(i).(j) <-  p2.heap.(i-Array.length p1.vars).(j);				
			if i < p1.gvar && j > p1.bound then
					   p.heap.(i).(j) <-  p2.heap.(i).(j-Array.length p1.vars);									
	  done;
	done;
		let intersect_d1, intersect_d2 = p1.data.(3).d1 land p2.data.(3).d1,p1.data.(3).d2 land p2.data.(3).d2 in
		if intersect_d1 = 0 || intersect_d2 = 0 || (Info.is_equal p1.heap.(3).(4) && Info.is_equal p2.heap.(3).(4)) || (p1.threads.(0).pc = 9 ||p1.threads.(0).pc = 10 && not (Info.is_equal p2.heap.(3).(4)))  then
			[p], false
		else
			begin 
		[p],true
		end
end 
     
  let do_full_intersection p1 p2  thi = begin  
    let start1 = start_index p1 in
  let start2 = start_index p2 in 
   if start1 <> start2  then
    [],false
   else
     if !example_name = "CCAS" || !example_name = "RDCSS" then begin
			do_intersection_CCAS p1 p2 start1 start1 start1 thi
			end
       else
    do_intersection p1 p2 start1 start1 start1 thi
  end

(* ================================================================================================================================================================= *)

let create_set (head:Label.t) (tail:Label.t) (marked:Label.t)  = begin
 (* assert( 3 = Label.unpack head && 4 = Label.unpack tail );*)
  let c = create ~example:Q 1 [|head;tail|] [|marked|]  in
  let iNull, iHead, iTail = index c (-1) Label.nil, index c (-1) head, index c (-1) tail in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTail,iNull);(iHead,iTail)];
  c.heap.(iHead).(iTail) <-  Info.reach2;
  c.heap.(iTail).(iHead) <-  Info.none;
	c.heap.(iTail).(0) <-  Info.reach2;
	c.data.(iHead) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.data.(iTail) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.cut.(iHead)  <- {r1 = Info.none; d = {d1 = 15;d2 = 15; d3 = (0,4) }; };
	c.cut.(iTail)  <- {r1 = Info.none; d = {d1 = 15;d2 = 15; d3 = (0,4) }; };
	c.scope.(iHead) <- 1;
	c.scope.(iTail) <- 1;
  [c]
end
 let create_ccas (a:Label.t) = begin
 (* assert( 3 = Label.unpack head && 4 = Label.unpack tail );*)
  let c = create_s ~example:Q 1 [|a|] in
  let iNull, iA = index c (-1) Label.nil, index c (-1) a in
  [c]
end
 let create_lock_set (head:Label.t) (tail:Label.t)   = begin
 (* assert( 3 = Label.unpack head && 4 = Label.unpack tail );*)
  let c = create_s ~example:Q 1 [|head;tail|]   in
  let iNull, iHead, iTail = index c (-1) Label.nil, index c (-1) head, index c (-1) tail in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTail,iNull);(iHead,iTail)];
  c.heap.(iHead).(iTail) <-  Info.reach2;
  c.heap.(iTail).(iHead) <-  Info.none;
	c.heap.(iTail).(0) <-  Info.reach2;
	c.data.(iHead) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.data.(iTail) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.cut.(iHead)  <- {r1 = Info.none; d = {d1 = 15;d2 = 15; d3 = (0,4) }; };
	c.cut.(iTail)  <- {r1 = Info.none; d = {d1 = 15;d2 = 15; d3 = (0,4) }; };
	c.scope.(iHead) <- 1;
	c.scope.(iTail) <- 1;
  [c]
end
 
   
let create_unordered_set (head:Label.t) (tail:Label.t) (s:Label.t)  = begin
 (* assert( 3 = Label.unpack head && 4 = Label.unpack tail );*)
  let c = create ~example:Q 1 [|head;tail|] [|s|] in
  let iNull, iHead, iTail = index c (-1) Label.nil, index c (-1) head, index c (-1) tail in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTail,iNull);(iHead,iTail)];
  c.heap.(iHead).(iTail) <-  Info.reach2;
  c.heap.(iTail).(iHead) <-  Info.none;
	c.heap.(iTail).(0) <-  Info.reach2;
	c.data.(iHead) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.data.(iTail) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.cut.(iHead)  <- {r1 = Info.none; d = {d1 = 15;d2 = 15; d3 = (0,4)}; };
	c.cut.(iTail)  <- {r1 = Info.none; d = {d1 = 15;d2 = 15; d3 = (0,4)}; };
	c.scope.(iHead) <- 1;
	c.scope.(iTail) <- 1;
  [c]
end
  

let create_elim_stack (s:Label.t) (eHead:Label.t) (eTail:Label.t) = begin
  assert( 3 = Label.unpack s );
  let c = create_s ~example:Q 1 [|s;eHead;eTail|] in
  let iTop = index c (-1) s in
	let iHead = index c (-1) eHead in
  let iTail = index c (-1) eTail in
  c.data.(iHead) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.data.(iTail) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.data.(iTop) <- {d1 = 1;d2 = 1; d3 = (0,4)};
  c.heap.(iTop).(0) <- Info.equal;
	c.heap.(0).(iTop) <- Info.equal;
	c.scope.(iTop) <- 1;
	c.heap.(iHead).(iTail) <- Info.reach2;
  c.heap.(iTail).(1) <- Info.reach2; 
	[c]
end
 
let create_elim_queue (head:Label.t) (tail:Label.t) (eHead:Label.t)  = begin
  let c = create_s ~example:Q 1 [|head;tail;eHead|]  in
  let iNull, iHead, iTail, ehead = index c (-1) Label.nil, index c (-1) head, index c (-1) tail, index c (-1) eHead in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTail,iNull);(iHead,iTail)];
  c.heap.(iHead).(iNull) <- Info.reach_q;
  c.heap.(iTail).(iNull) <- Info.reach_q;
	c.data.(iHead) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.data.(iTail) <- {d1 = 1;d2 = 1; d3 = (0,4)};
  c.heap.(iHead).(iTail) <- Info.equal;
  c.heap.(iTail).(iHead) <- Info.equal;
	c.heap.(ehead).(1) <- Info.reach2;
	c.data.(ehead) <- {d1 = 1;d2 = 1; d3 = (0,4)};
  [c]
end   
  
let mark_assign (lx:Label.t) (d:int) p thi : t list = begin
    (* x.data := d *)
		let x = index p thi lx in
		(*in the case of no cut attribute*)
		if p.cut.(x) = empty_attribute then 
			begin	
		   p.data.(x) <- {d1 = d; d2 = p.data.(x).d2; d3 = p.data.(x).d3};
       for i = 0 to p.bound do
			   if Info.is_equal p.heap.(i).(x) then
				  p.data.(i) <- p.data.(x);
	     done;
		end
		else begin
			let att = p.cut.(x) in
			p.cut.(x) <- {r1 = att.r1; d = {d1 = d; d2 = att.d.d2; d3 = att.d.d3};}
		end;
	[p]
end
let strengthen_mark_assign (lx:Label.t) (d:int) p thi : t list = begin
	let p1 = clone p in
	_kill p1 5;
	_kill p1 7;
	[p1]
end
let create_stack (s:Label.t) = begin
  assert( 3 = Label.unpack s );
  let c = create_s ~example:Q 1 [|s|] in
  let iTop = index c (-1) s in
  c.heap.(iTop).(0) <- Info.equal;
	c.heap.(0).(iTop) <- Info.equal;
	c.data.(iTop) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.data.(0) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.scope.(iTop) <- 1;
	[c]
end
  
let create_twolock_queue (head:Label.t) (tail:Label.t) (hLock:Label.t) (tLock:Label.t) = begin
  let c = create_s ~example:Q 1 [|head;tail;hLock;tLock|] in
  let iNull, iHead, iTail, iH, iT = index c (-1) Label.nil, index c (-1) head, index c (-1) tail, index c (-1) hLock, index c (-1) tLock in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTail,iNull);(iHead,iTail);(iH,iT);(iT,iH);(iHead,iT);(iHead,iH)];
  c.heap.(iHead).(iNull) <- Info.reach_q;
  c.heap.(iTail).(iNull) <- Info.reach_q;
		c.data.(iHead) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.data.(iTail) <- {d1 = 1;d2 = 1; d3 = (0,4)};
  c.heap.(iHead).(iTail) <- Info.equal;
  c.heap.(iTail).(iHead) <- Info.equal;
  [c]
end  
  
let create_queue (head:Label.t) (tail:Label.t) = begin
  let c = create_s ~example:Q 1 [|head;tail|] in
  let iNull, iHead, iTail = index c (-1) Label.nil, index c (-1) head, index c (-1) tail in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTail,iNull);(iHead,iTail)];
  c.heap.(iHead).(iNull) <- Info.reach_q;
  c.heap.(iTail).(iNull) <- Info.reach_q;
		c.data.(iHead) <- {d1 = 1;d2 = 1; d3 = (0,4)};
	c.data.(iTail) <- {d1 = 1;d2 = 1; d3 = (0,4)};
  c.heap.(iHead).(iTail) <- Info.equal;
  c.heap.(iTail).(iHead) <- Info.equal;
  [c]
end    
  
let create_hw_queue (head:Label.t) (back:Label.t) = begin
  let c = create_s ~example:Q 1 [|head;back|] in
  let iNull, iHead, iBack = index c (-1) Label.nil, index c (-1) head,index c (-1) back in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iBack,iNull);(iHead,iBack)];
  c.heap.(iHead).(iNull) <- Info.reach_hw_q;
  c.heap.(iBack).(iNull) <- Info.reach_hw_q;
	c.heap.(iHead).(iBack) <- Info.equal;
  c.heap.(iBack).(iHead) <- Info.equal;
  [c]
end  	
	
let test p =   p.observer = Init && Info.get_beta_d2 p.heap.(3).(6) = 2
	
let test2 p =  p.data.(6).d2 <> 2  && p.data.(5).d2 <> 2 && Info.get_beta_d2 p.heap.(3).(4) <> 2 && Info.get_beta_d2 p.heap.(3).(5) <> 2 && Info.get_beta_d2 p.heap.(3).(6) <> 2
&& Info.get_beta_d2 p.heap.(5).(4) <> 2 && Info.get_beta_d2 p.heap.(5).(6) <> 2 && Info.get_beta_d2 p.heap.(6).(4) <> 2

let uniform_attribute att = begin
let l =  {r1 = Info.reach1; d = {d1 = 2; d2 = att.d.d2; d3 = (0,4)};} in
if !example_name = "Vechev" then
	local_attribute
	else
l
end

let clean p = begin

  for i = 5 to p.bound do
    if p.cut.(i) <> empty_attribute then p.cut.(i) <- if !example_name = "Unordered" then local_unordered_attribute else (uniform_attribute p.cut.(i));
  done;
for i = 3330 to p.bound do
	  if p.data.(i).d2 = 2 then p.data.(i) <- {d1 = 1; d2 = p.data.(i).d2; d3 = p.data.(i).d3};
	done;
   if !example_name = "THarris" then begin  
     if p.threads.(0).pc = 17 then if (p.cut.(7) <> empty_attribute || p.cut.(8) <> empty_attribute) then begin clean_variable p 7; clean_variable p 8; end;
     if List.mem p.threads.(0).pc [34] then  if (p.cut.(10) <> empty_attribute || p.data.(10).d1 = 2 || p.cut.(9) <> empty_attribute || p.data.(9).d1 = 2) then begin clean_variable p 7;clean_variable p 8 end; 
     if List.mem p.threads.(0).pc [35;36] then  if (p.cut.(9) <> empty_attribute || p.data.(9).d1 = 2 || p.cut.(10) <> empty_attribute || p.data.(10).d1 = 2) then begin clean_variable p 7; clean_variable p 8; clean_variable p 9; clean_variable p 10 end; 
     if List.mem p.threads.(0).pc [37;23] then  if (p.cut.(7) <> empty_attribute || p.data.(7).d1 = 2 || p.cut.(8) <> empty_attribute || p.cut.(9) <> empty_attribute) then begin clean_variable p 7; clean_variable p 8; clean_variable p 9; clean_variable p 10 end; 
     if List.mem p.threads.(0).pc [32] then  if (p.cut.(7) <> empty_attribute || p.data.(7).d1 = 2 ||  p.cut.(9) <> empty_attribute) then begin _kill p 7; clean_variable p 8; clean_variable p 9; clean_variable p 10 end; 
     if List.mem p.threads.(0).pc [17] && Info.get_none_ord p.heap.(11).(5) = 2 &&  (p.cut.(7) <> empty_attribute || p.data.(7).d1 = 2 || p.cut.(8) <> empty_attribute || p.cut.(9) <> empty_attribute) then begin clean_variable p 7;clean_variable p 8 end; 
     if List.mem p.threads.(0).pc [22;25] then  if (p.data.(9).d1 = 2 ||  p.cut.(9) <> empty_attribute) then begin _kill p 7; clean_variable p 8; clean_variable p 9; clean_variable p 10 end; 
     
   end; 
  if !example_name = "Vechev_CAS" then begin  

		if List.mem p.threads.(0).pc [17;23] then  if (p.data.(5).d1 = 2 || p.cut.(5) <> empty_attribute || p.cut.(6) <> empty_attribute) then begin _kill p 5; _kill p 6; _kill p 7 end;
    if List.mem p.threads.(0).pc [21] then  if (p.cut.(5) <> empty_attribute || p.data.(5).d1 = 2) then begin _kill p 5; end;  
    if List.mem p.threads.(0).pc [22] then  if (p.cut.(5) <> empty_attribute || p.data.(5).d1 = 2) then begin _kill p 5; end;  
    if List.mem p.threads.(0).pc [22] then  if (p.cut.(6) <> empty_attribute || p.data.(6).d1 = 2) then begin _kill p 6;_kill p 7 end; 
	
  end;
  if !example_name = "HMset" then begin 
     
     if List.mem p.threads.(0).pc [14;23;20] then  if (p.data.(5).d1 = 2 || p.cut.(5) <> empty_attribute || p.cut.(6) <> empty_attribute) then begin _kill p 5; _kill p 6; _kill p 7 end;
     if List.mem p.threads.(0).pc [22] then  if (p.cut.(5) <> empty_attribute || p.data.(5).d1 = 2) then begin _kill p 5; end;  
     if List.mem p.threads.(0).pc [22] then  if (p.cut.(6) <> empty_attribute || p.data.(6).d1 = 2) then begin _kill p 6;_kill p 7 end; 
       
        
       
    end;  
  if !example_name = "MMichael" then begin  
     if List.mem p.threads.(0).pc [14;23;20] then  if (p.data.(5).d1 = 2 || p.cut.(5) <> empty_attribute || p.cut.(6) <> empty_attribute) then begin _kill p 5; _kill p 6; _kill p 7 end;
     if List.mem p.threads.(0).pc [22] then  if (p.cut.(5) <> empty_attribute || p.data.(5).d1 = 2) then begin _kill p 5; end;  
     if List.mem p.threads.(0).pc [22] then  if (p.cut.(6) <> empty_attribute || p.data.(6).d1 = 2) then begin _kill p 6;_kill p 7 end; 
     if List.mem p.threads.(0).pc [8] then  if (p.data.(5).d1 = 2 || p.cut.(5) <> empty_attribute || p.cut.(6) <> empty_attribute ) then begin _kill p 5; _kill p 6; _kill p 7 end;
     if List.mem p.threads.(0).pc [11] then  if (p.data.(5).d1 = 2 || p.cut.(5) <> empty_attribute) then begin _kill p 5; end;
     
  end;    
end
let test3 p = 
  p.data.(6).d2 = 2; 

(*
(* ===================================================================================TESTTING========================================================================*)
let test p = 
	print_string "\n==================================================================================TESTTING========================================================================\n";
  let p1 = clone p in
	let p2 = clone p in
	let a_label = (Info.next_pointer, Info.lessthan_order, [Info.notmarked_data; Info.notlocked_data]) in
	let b_label = (Info.next_pointer, Info.lessthan_order, [Info.notmarked_data; Info.notlocked_data]) in
	
	let a_label_1 = (Info.next_pointer, Info.none_order, [Info.none_data; Info.none_data]) in
	let empty =   (Info.none_pointer, Info.none_order, [Info.none_data; Info.none_data]) in
	let ord = Info.lessthan_order in
	let cell = Info.create_entire_cell a_label b_label ord in 
	let single_cell = Info.create_entire_cell a_label_1 empty Info.none_order in 
	p1.heap.(3).(5) <- cell;
	p1.heap.(5).(6) <- cell;
	p1.heap.(6).(7) <- cell;
	p1.heap.(7).(4) <- cell;
	p1.heap.(3).(4) <- Info.none;
	p1.heap.(4).(0) <- single_cell;
	p1.data.(5) <- [Info.notmarked_data; Info.notlocked_data];
	p1.data.(6) <- [Info.notmarked_data; Info.notlocked_data];
	p1.data.(7) <- [Info.notmarked_data; Info.notlocked_data];
	p1.cut.(5) <- (Info.equal, [Info.none_data; Info.none_data], Info.none);
	p1.cut.(6) <- (Info.equal, [Info.none_data; Info.none_data], Info.none);
	p1.cut.(7) <- (Info.equal, [Info.none_data; Info.none_data], Info.none);
	print_cons p1;
	p2.heap.(3).(5) <- cell;
	p2.heap.(5).(6) <- Info.equal;
	p2.heap.(6).(5) <- Info.equal;
	p2.heap.(6).(7) <- cell;
	p2.heap.(7).(4) <- cell;
	p2.heap.(3).(4) <- Info.none;
	p2.heap.(4).(0) <- single_cell;
	p2.data.(5) <- [Info.notmarked_data; Info.notlocked_data];
	p2.data.(6) <- [Info.notmarked_data; Info.notlocked_data];
	p2.data.(7) <- [Info.notmarked_data; Info.notlocked_data];
	p2.cut.(5) <- (Info.equal, [Info.none_data; Info.none_data], Info.none);
	p2.cut.(6) <- (Info.equal, [Info.none_data; Info.none_data], Info.none);
	p2.cut.(7) <- (Info.equal, [Info.none_data; Info.none_data], Info.none);
	pure_strengthen p2;
	print_cons p2;
	let p = join_cons_full p1 p2 in
	print_cons p
*)