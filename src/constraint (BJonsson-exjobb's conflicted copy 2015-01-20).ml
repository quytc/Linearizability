let sprintf = Printf.sprintf
exception BreakLoop of int
let debug = false
let debugJOIN = false
let debugJOIN_Info = false
let debugPermute = false
let debugEXTEND = false

(* Global counter, for identification *)  
let maxID = ref (-1)

type ex = Q | Rest

let b = Buffer.create 20000 (* Buffer for the to_dot printing *)
let bp = Buffer.create 700 (* Buffer for the permutations. *)

type lockstate = Me | Others | Unlocked
let string_of_lockstate = function | Me -> "Me" | Others -> "Others" | Unlocked -> "Unlocked"
let char_of_lockstate = function | Me -> '*' | Others -> 'o' | Unlocked -> 'u'

(* ========================================================================== *)
type thread = {
    mutable pc: int; 
		mutable interf_pc: int;
    mutable promise: Promise.t;
    mutable return: Data.t;
    (* mutable stack: Stack.t; *)
    bits: bool array;
    mutable trans: string array;

    mutable locks: lockstate array;

    mutable lbound: int;
    mutable range: int;
  }
      
let thread_create bits locks lbound = begin
  { pc=0;
	  interf_pc = 0;
    promise=Promise.NoPromise;
    return=Data.top;
    bits=(Array.make bits false);
    trans=[||];
    locks = (Array.make locks Unlocked);
    lbound=lbound; range=0;
  } 
end
let thread_clone th = {th with bits=Array.copy th.bits; locks=Array.copy th.locks;}
      
let thread_to_dot th buf = begin
  Buffer.add_string buf "PC: ";
  Buffer.add_string buf (string_of_int th.pc);
  Buffer.add_string buf "\tPromise: ";
  Promise.buffer buf th.promise;
  Buffer.add_string buf "\tReturn: ";
  Data.buffer buf th.return;
  Buffer.add_string buf "\tBits:[";
  Array.iter (fun bit -> Buffer.add_char buf (if bit then 'T' else 'F')) th.bits;
  Buffer.add_char buf ']';
  Buffer.add_string buf "\tLocks:[";
  Array.iter (fun lock -> Buffer.add_char buf (char_of_lockstate lock)) th.locks;
  Buffer.add_char buf ']';
end

let string_of_thread th = 
  sprintf "PC: %-2d | Promise: %-18s | Return: %c | Bits:[|%s] | Locks:[|%s]\tLower bound: %-2d -- Range: %d"
    th.pc (Promise.string_of th.promise) (Data.char_of th.return)
    (Array.fold_left (sprintf "%s%-5B|") "" th.bits) (Array.fold_left (fun acc lock -> sprintf "%s%-8s|" acc (string_of_lockstate lock)) "" th.locks)
    th.lbound th.range
    
let compare_thread th1 th2 =
  let cv1 = Pervasives.compare th1.pc th2.pc in
  if cv1 <> 0 then cv1 else
  let cv2 = Promise.compare th1.promise th2.promise in
  if cv2 <> 0 then cv2 else 
  let cv3 = Data.compare th1.return th2.return in
  if cv3 <> 0 then cv3 else 
  let cv4 = Pervasives.compare th1.bits th2.bits in
  if cv4 <> 0 then cv4 else 
  Pervasives.compare th1.locks th2.locks

(* ========================================================================== *)

type t = {
    
    mutable observer: Observer.state;      (** The state of the observer *)
    mutable nth:int;
    mutable threads: thread array;
    mutable heap: Info.t array array;
		mutable scope: int array array;
		mutable data: int array array;
    mutable bound: int;
    gvar: int;
    colors:int;
		mutable cutpoints: int;
    mutable vars: Label.t array;
    mutable translation: string array;
    
    mutable permutation: int array;
    mutable iterator: int array;
    mutable in_queue: bool;
    mutable in_slice: bool;
    id:int;
    example:ex;
    mutable join_count:int;
    mutable messages:string list;
    mutable parents: t list;

    mutable encoding: string;
  } 

let create ?(example=Rest) nth gvars gcolors bits locks = incr maxID;
  let gvar = 3 + Array.length gvars in (* 3 = null, bottom and free *)
  let colors = Array.length gcolors in
  let bound = gvar + colors - 1 in
  let bound' = bound+1 in
  let h = Array.make_matrix bound' bound' Info.none in
	let s = Array.make_matrix bound' 1 0 in
	let d = Array.make_matrix bound' 1 0 in
  for i=0 to bound do for j=0 to bound do h.(i).(j) <- (if i=j then Info.equal else Info.none); done; done;
  let threads = Array.init nth (fun _ -> thread_create bits locks (gvar + colors)) in
  {
  example=example;
  observer = Observer.init;
  nth = nth;
  threads = threads;
  heap = h;
	scope = s;
	data = d;
  gvar = gvar;
	cutpoints = 0;
  colors = colors;
  bound = bound;
	vars = [||];
  permutation=(Array.init nth (fun i -> i));
  iterator=(Array.init bound' (fun i -> i));

  translation = Array.append
    (Array.map Label.string_of (Array.append [|Label.nil;Label.bottom;Label.free(* ;Label.locked *)|] gvars))
    (Array.map Data.string_of gcolors);
  
  in_queue=false;
  in_slice=false;
  
  id = (!maxID);
  join_count = 0;
  messages = [];
  parents = [];

  encoding="";
}

let _clone t id =
  { t with id=id;
    threads = Array.map thread_clone t.threads;
(*     heap = Array.map (Array.map Info.clone) t.heap; *)
    heap = Array.map Array.copy t.heap;
		scope = Array.map Array.copy t.scope;
		data = Array.map Array.copy t.data;
    translation = Array.copy t.translation;
    permutation = Array.copy t.permutation;
    iterator = Array.copy t.iterator;
    (* will copy the rest *) 
  }

let clone t = incr maxID; _clone t (!maxID)

let string_of t = 
  sprintf "(%d)[Observer=%s]\n%s" t.id (Observer.string_of_state t.observer)
    (Array.fold_left (fun acc thi -> sprintf "%s\t%s\n" acc (string_of_thread t.threads.(thi))) "" t.permutation)

(* ========================================================================================================= *)
(* =====================                        Utilities                           ======================== *)
(* ========================================================================================================= *)
let is_q p = match p.example with Q -> true | _ -> false (* p.gvar > 4 *)

let id t = t.id
let observer t = t.observer
let set_observer t obs = t.observer <- obs
    
let nthreads p = p.nth
let gvar p = p.gvar
let var p = Array.length p.vars
let set_in_queue t v = t.in_queue <- v
let in_queue t = t.in_queue
let set_in_slice t v = t.in_slice <- v
let in_slice t = t.in_slice
    
let set_parent p p' = if !Globals.trace then p.parents <- [_clone p' p'.id]; ()
let log t message = if !Globals.trace then t.messages <- (Lazy.force message)::t.messages; ()
let pc p thi = p.threads.(thi).pc
let get_mark p i = p.data.(i).(0)
let bound p = p.bound
let cutpoints p = p.cutpoints
let interf_pc p thi = p.threads.(thi).interf_pc
let set_pc p thi pc = p.threads.(thi).pc <- pc  
let logical_pc p thi = p.threads.(p.permutation.(thi)).pc
let physical_thread p thi = p.permutation.(thi)
let promise p thi = p.threads.(thi).promise
let set_promise p thi prom = p.threads.(thi).promise <- prom
let reset_prom p thi = set_promise p thi Promise.NoPromise
let set_return p thi d = p.threads.(thi).return <- d
let is_uptodate bit thi p = p.threads.(thi).bits.(bit)
let set_bit (v:bool) (bit:int) (p:t) (thi:int) = p.threads.(thi).bits.(bit) <- v
let make_uptodate bit thi p = set_bit true bit p thi
let reset_bits (bit:int) (p:t) = for thi=0 to p.nth-1 do set_bit false bit p thi done

    
let rec iter_trace p f acc = begin
  f p;
  List.iter (fun papa -> if not(List.mem papa acc) (*logically*) then iter_trace papa f (p::acc);) p.parents;
(*   List.iter (fun papa -> if not(List.memq papa acc) (\*physically*\) then iter_trace papa f (p::acc);) p.parents; *)
end
    

exception Stop (* to break foldings and iterations *)
exception Found of string

let __t p i = if i < p.gvar + p.colors then p.translation.(i) else begin
  try
    for thi=0 to p.nth - 1 do
      let th = p.threads.(thi) in
      if i >= th.lbound && i < th.lbound + th.range then raise (Found (sprintf "%s.%d" th.trans.(i-th.lbound) thi));
    done;
    "unknown"
  with Found trans -> trans 
end


(* =================================================================================== *)
let index p thi v = begin (* thi is a physical index *)
  if Label.is_global v
  then Label.unpack v
  else begin
    let shift = Label.unpack v in
    let th = p.threads.(thi) in
    assert( shift <= th.range );
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

exception Compare of int
let inspect_gworld p1 p2 = 
     Pervasives.compare p1.gvar p2.gvar lor 
     Pervasives.compare p1.colors p2.colors lor 
     Pervasives.compare p1.bound p2.bound
let print_cons p = begin
  	print_string "\n\n";
	print_string "PC: "; print_int p.threads.(0).pc; print_string "\n";
	print_string "========================================================================================================================================\n";
	print_string "         ";
	 for i=0 to p.gvar - 1 do 
	  print_string (p.translation.(i));
		print_string "         ";
	 done;
	for i=0 to (Array.length p.vars) - 1 do 
	  print_string (Label.string_of p.vars.(i)); print_string "         ";
	 done;	
	for i=0 to p.cutpoints - 1 do 
	  print_string "c";print_int i; print_string "        "
	  done;	
	print_string "\n";
	print_string "----------------------------------------------------------------Scope---------------------------------------------------------------------\n";
				print_string "         ";
		for r=0 to  p.bound do 
	  print_int p.scope.(r).(0);print_string "         ";
	 done;
	print_string "\n";
		print_string "----------------------------------------------------------------Marked------------------------------------------------------------------\n";
				print_string "         ";
		for r=0 to  p.bound do 
	  print_int p.data.(r).(0);print_string "         ";
	 done;	
  print_string "\n--------------------------------------------------------------Info----------------------------------------------------------------------\n";
(*
	  for i = 0 to p.bound do
			if i < p.gvar then begin  print_string (p.translation.(i));print_string "        " end
			else
			if i < p.gvar + (Array.length p.vars) then begin print_string (Label.string_of p.vars.(i- p.gvar)); print_string "        " end
			else  begin print_string "c"; print_int (i- p.gvar - (Array.length p.vars)); print_string "        " end;
			
		for j=0 to p.bound do			  
			if Info.is_none p.heap.(i).(j) <> 0 && j < p.gvar then begin assert(Debug.print "%s %s %s" Debug.yellow  (p.translation.(j)) Debug.noColor;true);Info.print_cell p.heap.(i).(j); end
			else
				 if Info.is_none p.heap.(i).(j) <> 0 && j >= p.gvar then begin assert(Debug.print "%s %s %s" Debug.yellow  (Label.string_of p.vars.(j-p.gvar)) Debug.noColor;true);Info.print_cell p.heap.(i).(j); end
			else
				Info.print_cell p.heap.(i).(j);
			 (*if Info.is_reach p.heap.(i).(j) == 0 && List.length(Info.get_b_label p.heap.(i).(j)) > 0 then*)
			if (Info.is_none p.heap.(i).(j) <> 0 && Info.is_equal p.heap.(i).(j) <> 0) || Info.ord p.heap.(i).(j) == 2 then 
				print_string "      "
				else
				
			print_string "         "
		done;
		print_string "\n-----------------------------------------------------------------------------------------\n";
		done;
*)

	print_string "\n\n";
  let  rec print v1 = begin
		let time = ref 0 in
		let next_var = ref 0 in
		if v1 < p.gvar then  assert(Debug.print "%s %s %s" Debug.yellow  (p.translation.(v1) ^ ":" ^ string_of_int(v1)) Debug.noColor;true)
			     else
				   if v1 >= p.gvar then begin
						  if v1 <= p.bound - p.cutpoints then assert(Debug.print "%s %s %s" Debug.yellow  (Label.string_of p.vars.(v1-p.gvar)  ^ ":" ^ string_of_int(v1)) Debug.noColor;true) 
							else
								assert(Debug.print "%s %s %s" Debug.red  ("C"  ^ ":" ^ string_of_int(v1- p.bound + p.cutpoints)) Debug.noColor;true) 
					 end;
					
		if v1 == 3 then begin
		for i = 0 to  p.bound do
			if Info.is_equal p.heap.(v1).(i) == 0 && i <> v1  && v1 == 3 then begin
									print_string ",";
				if i < p.gvar then  assert(Debug.print "%s %s %s" Debug.yellow  ((p.translation.(i)) ^ ":" ^ string_of_int(i)) Debug.noColor;true)
			     else
				   if i >= p.gvar then  
						if i <= p.bound - p.cutpoints then
						  assert(Debug.print "%s %s %s" Debug.yellow  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true)
						else
							assert(Debug.print "%s %s %s" Debug.red  ("C"  ^ ":" ^ string_of_int(i- p.bound + p.cutpoints)) Debug.noColor;true)
			end;
		done;	
		end;
		
				for i = 0 to  p.bound do
			if Info.is_reach p.heap.(v1).(i) == 0 && !time == 0 then
				begin
					print_string "  "; Info.print_cell p.heap.(v1).(i); print_string "   ";
					time := 1;
					next_var := i;
				end
			else
				if Info.is_reach p.heap.(v1).(i) == 0  then begin
					if i < p.gvar then  assert(Debug.print "%s %s %s" Debug.yellow  ((p.translation.(i)) ^ ":" ^ string_of_int(i)) Debug.noColor;true)
			     else
				   if i >= p.gvar then 
						 if i <= p.bound - p.cutpoints then assert(Debug.print "%s %s %s" Debug.yellow  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true)
						 else
							assert(Debug.print "%s %s %s" Debug.red  ("C"  ^ ":" ^ string_of_int(i- p.bound + p.cutpoints)) Debug.noColor;true);
					print_string ",";
				end;
				
		done;	
		if !next_var <> 0 then print !next_var;
		end
    in
	
				print 3;
				print_string "\n\n\n\n\n\n";
end


let print_merge_cons p p1 p2 = begin
	print_string "\n\n";
	print_string "PC: "; print_int p.threads.(0).pc; print_string "\n";
	print_string "===================================MERGE==========================================\n";
	print_string "       ";
	 for i=0 to p1.gvar - 1 do 
	  print_string (p.translation.(i));
		print_string "      ";
	 done;
	for i=0 to (Array.length p1.vars) - 1 do 
	  print_string (Label.string_of p1.vars.(i)); print_string "      ";
	 done;
	
	for i=0 to p1.cutpoints - 1 do 
	  print_string "c";print_int i; print_string "      " 
	  done;
	
		for i=0 to (Array.length p2.vars) - 1 do 
	  print_string (Label.string_of p2.vars.(i)); print_string "      ";
	 done;
	
	for i=0 to p2.cutpoints - 1 do 
	  print_string "c";print_int i; print_string "      "
	  done;	
		
	print_string "\n";
	print_string "--------------------------------Scope----------------------------------------\n";
				print_string "       ";
		for r=0 to  p.bound do 
	  print_int p.scope.(r).(0);print_string "      ";
	 done;
	print_string "\n";
		print_string "--------------------------------DATA----------------------------------------\n";
				print_string "       ";
		for r=0 to  p.bound do 
	  print_int p.data.(r).(0);print_string "      ";
	 done;
	print_string "\n";
		print_string "\n------------------------------Info-------------------------------------------\n";
	
	  for i = 0 to p1.bound do
			if i < p1.gvar then begin  print_string (p1.translation.(i));print_string "      " end
			else
			if i < p1.gvar + (Array.length p1.vars) then begin print_string (Label.string_of p1.vars.(i- p1.gvar)); print_string "        " end
			else  begin print_string "c"; print_int (i- p1.gvar - (Array.length p1.vars)); print_string "      " end;
			
		for j=0 to p.bound do			  
			 Info.print_cell p.heap.(i).(j);
			print_string "      ";	 
		done;
				print_string "\n---------------------------------------------------------------------------\n";		
		done;
		 for i = p1.bound+1 to p.bound do
     if i <=  p1.bound + (Array.length p2.vars) then begin print_string (Label.string_of p1.vars.(i- p1.bound-1)); print_string "        " end
			else  begin print_string "c"; print_int (i- 1 -p2.bound-(Array.length p2.vars)); print_string "      " end;
	
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
						if v1 > p1.bound then begin 
							  if v1 <= p.bound - p.cutpoints then assert(Debug.print "%s %s %s" Debug.green  ((Label.string_of p.vars.(v1-p.gvar)) ^":"^ string_of_int(v1)) Debug.noColor;true)
								else
								     assert(Debug.print "%s %s %s" Debug.blue  ("C" ^":"^ string_of_int(v1-p.bound)) Debug.noColor;true)
								end
						 
						else
							assert(Debug.print "%s %s %s" Debug.yellow  (Label.string_of p.vars.(v1-p.gvar)  ^ ":" ^ string_of_int(v1)) Debug.noColor;true);
		
		if v1 == 3 then begin
		for i = 0 to  p.bound do
			if Info.is_equal p.heap.(v1).(i) == 0 && i <> v1  && v1 == 3 then begin
				if i < p.gvar then  assert(Debug.print "%s %s %s" Debug.yellow  ((p.translation.(i)) ^ ":" ^ string_of_int(i)) Debug.noColor;true)
			     else
				   if i >= p.gvar then  
						if i > p1.bound then begin 
							  if i <= p.bound - p.cutpoints then assert(Debug.print "%s %s %s" Debug.green  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true)
								else
								     assert(Debug.print "%s %s %s" Debug.blue  ("C" ^":"^ string_of_int(i-p.bound)) Debug.noColor;true)
								end
						 
						else
						assert(Debug.print "%s %s %s" Debug.yellow  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true);
			end;
		done;	
		end;
		
				for i = 0 to  p.bound do
			if Info.is_reach p.heap.(v1).(i) == 0 && !time == 0 then
				begin
					print_string "  "; Info.print_cell p.heap.(v1).(i); print_string "   ";
					time := 1;
					next_var := i;
				end
			else
				if Info.is_reach p.heap.(v1).(i) == 0  then begin
					if i < p.gvar then  assert(Debug.print "%s %s %s" Debug.red  ((p.translation.(i)) ^ ":" ^ string_of_int(i)) Debug.noColor;true)
			     else
				   if i >= p.gvar then  
						if i > p1.bound then 
							   begin if i <= p.bound - p.cutpoints
								          then assert(Debug.print "%s %s %s" Debug.green  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true)
								       else
												assert(Debug.print "%s %s %s" Debug.red  ("C" ^":"^ string_of_int(i-p.bound)) Debug.noColor;true);
								 end
						else
						assert(Debug.print "%s %s %s" Debug.yellow  ((Label.string_of p.vars.(i-p.gvar)) ^":"^ string_of_int(i)) Debug.noColor;true);
					print_string ",";
				end;
				
		done;	
		if !next_var <> 0 then print !next_var;
		end
    in
	print_string "";
				print 3;
end

let update_scope p = begin
	(*update scope of local variables in p to local*)
	for i = p.gvar to p.bound do
		if p.scope.(i).(0) <> 2 then p.scope.(i).(0) <- 1
	done;
  for i = 0 to p.gvar-1 do
		p.scope.(i).(0) <- 0
	done;
	(*local variables reached from global are updated to global*)
    for i = 0 to p.bound do
	  for j = 0 to p.bound do
       if (Info.is_reach p.heap.(i).(j) == 0 || Info.is_equal p.heap.(i).(j) == 0) && p.scope.(i).(0) == 0 then
				p.scope.(j).(0) <- 0     					
	  done;
       done;
 for i = 0 to p.bound do
	  for j = 0 to p.bound do
       if (Info.is_reach p.heap.(i).(j) == 0 || Info.is_equal p.heap.(i).(j) == 0) && p.scope.(i).(0) == 0 then
				p.scope.(j).(0) <- 0     					
	  done;
       done;
  	p
end	
(* will update the matrix in place *)
let _add p i j phi = begin
  assert( i <> j );
end

let is_cutpoint p x = begin
	update_scope p;
  let ret = ref 1 in
  if p.scope.(x).(0) == 1 then
    ret := 1
  else begin
	let z = ref (p.bound + 1) in
	for i = 0 to p.bound do
   if Info.is_reach p.heap.(i).(x) == 0  && !z == (p.bound + 1)  then z := i
			else
     if Info.is_reach p.heap.(i).(x) == 0  && !z <> (p.bound + 1)  then if Info.is_equal p.heap.(i).(!z) <> 0 then ret := 0 
	done;
	
	for i = 0 to 2 do
		if p.heap.(x).(i) == Info.equal then ret := 1
	done;
	
    for i = p.gvar + (Array.length(p.vars)) to p.bound do
      if x < p.gvar + (Array.length(p.vars)) && p.heap.(x).(i) == Info.equal then ret := 1
    done;
  for i = 0 to p.gvar + (Array.length(p.vars)) -1 do
    if x >= p.gvar + (Array.length(p.vars)) && p.heap.(x).(i) == Info.equal then ret := 1
  done;
  end;
	!ret
end

let _mergeover (p:t) x fro till = begin
	let isolated_second_thread_variable k = begin
  let ret = ref 0 in
	  for i = 3 to p.bound do
		  if (i <= fro || i > till) then
		    if Info.is_equal p.heap.(k).(i) == 0 then ret := 1
	 done;
	!ret
	end in
	if isolated_second_thread_variable x == 0 then 
		begin
     for i=0 to p.bound do
		  for j=0 to p.bound do
			  if Info.is_reach p.heap.(i).(x) == 0  && Info.is_reach p.heap.(x).(j) == 0 then 
					begin
					 p.heap.(i).(j) <- Info.merge_cell p.heap.(i).(x) p.heap.(x).(j) p.heap.(i).(j);	
					 (*if i and j are in the first thread, then strengthen is needed*)   
					 if isolated_second_thread_variable i == 1 && isolated_second_thread_variable j == 1 then
						begin
							for i1 = 0 to p.bound do
								for j1 = 0 to p.bound do
								  if Info.is_equal p.heap.(i1).(i) == 0 && Info.is_equal p.heap.(j1).(j) == 0 then
										p.heap.(i1).(j1) <- p.heap.(i).(j);
								done;
							done;
						end;
					end;    
	    done;
	   done;		
	 end
end

let is_cutpoint' p x fro till = begin
  	let ret = ref 1 in
  if p.scope.(x).(0) == 1 then
    ret := 1
  else begin	
		let z = ref (p.bound + 1) in
	for i = 0 to p.bound do
    if Info.is_reach p.heap.(i).(x) == 0  && p.scope.(i).(0) == 0 && !z == (p.bound + 1)  then z := i
	done;
	for i = 0 to p.bound do
      if Info.is_reach p.heap.(i).(x) == 0 && !z <> (p.bound + 1)  then
        if Info.is_equal p.heap.(i).(!z) <> 0 || Info.is_equal p.heap.(!z).(i) <> 0 then ret := 0 
	done;	
  end;	
	!ret
end
  
let copy_variable p x y = begin
	for i = 0 to p.bound do
	   p.heap.(i).(y) <- p.heap.(i).(x);
		 p.heap.(y).(i) <- p.heap.(x).(i);
	done;
	p.heap.(y).(y) <- Info.equal;
	p.scope.(y).(0) <- p.scope.(x).(0);
	p.data.(y).(0) <- p.data.(x).(0);
end

let add_cutpoint p = begin
let newbound = p.bound + 1 in
let newheap = Array.make_matrix (newbound+1) (newbound+1) Info.none in
let newscope = Array.make_matrix (newbound+1) (1) 1 in	
let newsdata = Array.make_matrix (newbound+1) (1) 0 in	
   for i = 0 to p.bound do
		newscope.(i).(0) <- p.scope.(i).(0);
		newsdata.(i).(0) <-p.data.(i).(0);
		for j = 0 to p.bound do
	  newheap.(i).(j) <- p.heap.(i).(j);
	done;
	done;	
p.heap <- newheap;
p.scope <-newscope;
p.data <- newsdata;
p.bound <- newbound ;
p.cutpoints <- p.cutpoints + 1;	
end


(*====================================================KILL CUTPOINT======================================================================*)
let kill_cutpoints p x = begin
let newbound = p.bound - 1 in
let newheap = Array.make_matrix (newbound+1) (newbound+1) Info.none in
let newscope = Array.make_matrix (newbound+1) (1) 1 in	
let newsdata = Array.make_matrix (newbound+1) (1) 0 in	
 for i = 0 to p.bound - p.cutpoints do
    newscope.(i).(0) <- p.scope.(i).(0);
    newsdata.(i).(0) <- p.data.(i).(0);
		for j = 0 to p.bound - p.cutpoints do
	  newheap.(i).(j) <- p.heap.(i).(j);
	  done;
	done;
  for i = 0 to p.bound  do
    if i < x  then begin newscope.(i).(0) <- p.scope.(i).(0); newsdata.(i).(0) <- p.data.(i).(0); end
		else
    if i > x then begin newscope.(i-1).(0) <- p.scope.(i).(0); newsdata.(i-1).(0) <- p.data.(i).(0); end;
		for j = 0 to p.bound do
			if i < x && j < x then
	       newheap.(i).(j) <- p.heap.(i).(j)
			else
			if i > x && j < x then
				 newheap.(i-1).(j) <- p.heap.(i).(j)
			else
       if i > x && j > x then
				 newheap.(i-1).(j-1) <- p.heap.(i).(j)
	  	 else
			  if i < x && j > x then
				 newheap.(i).(j-1) <- p.heap.(i).(j);
	  done;
done;			
p.heap <- newheap;
p.scope <-newscope;
p.data <-newsdata;
p.bound <- newbound ;
p.cutpoints <- p.cutpoints - 1;	  
end



(*Kill the variable from matrix p*)
let _kill (p:t) x = begin 
  let is_merged = ref 0 in
	for k = 3 to p.bound do
   if k <> x then 
		  if Info.is_equal p.heap.(x).(k) == 0 then is_merged := 1
  done;	
	if 	!is_merged == 0 && is_cutpoint p x == 0 then begin
		    add_cutpoint p;				
				copy_variable p x p.bound end	
	else		
	if !is_merged == 0 then 
		begin			
	    for i=0 to p.bound do
		    for j=0 to p.bound do
		    	if Info.is_reach p.heap.(i).(x) == 0  && Info.is_reach p.heap.(x).(j) == 0 then
           begin  
						  p.heap.(i).(j) <- Info.merge_cell p.heap.(i).(x) p.heap.(x).(j) p.heap.(i).(j);	
						  for i1 = 0 to p.bound do
								for j1 = 0 to p.bound do
								  if Info.is_equal p.heap.(i1).(i) == 0 && Info.is_equal p.heap.(j1).(j) == 0 then
										p.heap.(i1).(j1) <- p.heap.(i).(j);
								done;
							done;						
					 end;       
	       done;
	     done;	
    end;
	for i=0 to p.bound do	
		p.heap.(x).(i) <- Info.none; 
		p.heap.(i).(x) <- Info.none; 		
	done;
  p.heap.(x).(x) <- Info.equal;
  p.data.(x).(0) <- 0;
end

let _add_cutpoint (p:t) fro til = begin
  let ret = ref 0 in
  for x = fro +1 to til do
    let is_merged = ref 0 in
	  for k = 3 to p.bound do
		  if k <> x && (k <= fro || k > til) then
	      	if Info.is_equal p.heap.(x).(k) == 0 then is_merged := 1
	  done;
	  (*if there is no variable that is same as x*)
    if !is_merged == 0 && is_cutpoint' p x fro til == 0 then 
		 begin
      ret := !ret + 1;
			add_cutpoint p;				
      copy_variable p x p.bound;
     end;	
  done;
  !ret,p		
end
  
let make_new_cell (lx:Label.t) (p:t) (thi:int): t list = begin
  assert( Label.is_local lx );
  let x = index p thi lx in
	_kill p x;
  p.scope.(x).(0) <- 2;
  for i=0 to p.bound do
    if i <> x then begin 
			 p.heap.(i).(x) <- Info.none;
			 p.heap.(x).(i) <- Info.none;
	  end;
  done;
	p.heap.(x).(x) <- Info.equal;
	[p]
end

let next_equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x.next == y *)
    []
end

let inNextReference (lx:Label.t) p thi : t list = begin
    (* x.next is undefined *)
		let x= index p thi lx in
			if Info.is_reach p.heap.(x).(0) == 0 then 
				[p]
		else
      []
end

let nextReference (lx:Label.t) p thi : t list = begin
    (* x.next is defined *)				
		let x = index p thi lx in
		let res = ref 1 in
		for i = 0 to p.bound do
      if i <> x then 
		    begin 
         if Info.is_reach p.heap.(x).(i) == 0 && i > 2 then 
		     res := 0
	      end;
		done;
		if !res == 0 then 
			[p]
		else
      []
end

let equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x == y *)
		let x,y = index p thi lx, index p thi ly in	
			if Info.is_equal p.heap.(x).(y) == 0  then 
			[p]
		else
      []
end  

	let intersect_data x y = match x,y with
			| 2,2 -> 2
			| 11,2 -> 11
			| 2,11 -> 11
			| 2,0  -> 0
			| 0,2  -> 0
			| 0,0  -> 0
			| 11,11 -> 11
			| 10,3 -> 10
			| 3,10 -> 10
			| 10,10 -> 10
			| 3,3 -> 3
			| 0,3 -> 3
			| 3,0 -> 3
			| 10,4 -> 10
			| 4,10 -> 10
			| 11,4 -> 11
			| 4,11 -> 11
			| 4,4 -> 4
			| 2,3 -> 0
			| 3,2 -> 0
			| 3,4 -> 10
			| 4,3 -> 10
			| 2,4 -> 11
			| 4,2 -> 11
			| d,5 -> d
			| 5,d -> d
			| 5,5 -> 5
			| _,_ -> 1000
 let data_equality (lx:Label.t) (d:int) p thi : t list = begin
    (* x == d *)	
		let x = index p thi lx in	
		  let new_data = intersect_data p.data.(x).(0) d in
			if new_data <> 1000 then begin 
			   if new_data <> p.data.(x).(0) then begin
		     (*update the data to new_data*)
			    p.data.(x).(0) <- new_data;
					(*update data equality variables to x*)
					for i = 0 to p.bound do
				     if Info.is_equal p.heap.(i).(x) == 0 || Info.is_equal p.heap.(x).(i) == 0 then begin
						    p.data.(i).(0) <- new_data;
						   (*update relation point to x by new data*)
			         for j = 0 to p.bound do
				          if Info.is_reach p.heap.(j).(i) == 0 then
						         p.heap.(j).(i) <- Info.update_data_a_label p.heap.(j).(i) new_data;
				       done;
						 end;
				 done;			   
         [p]
			   end
			   else
				  [p]
			end
		else
      [] 
end
				
let data_inequality (lx:Label.t) (d:int) p thi : t list = begin
    (* x <> d *)
		let x = index p thi lx in	
   if p.data.(x).(0) <> d  then 
			[p]
		else
      []
end 								
												
																		    
let less_than (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x < y *)
		let x,y = index p thi lx, index p thi ly in		
		if Info.ord p.heap.(x).(y) == 2  then 
			[p]
		else
	  if Info.ord p.heap.(x).(y) == 3 && Info.ord p.heap.(y).(x) == 3 then
			begin 
				p.heap.(x).(y) <- Info.update_ord p.heap.(x).(y) 2;
			 (*it triger other ord relation, let update new ord relation now*)
       for i = 0 to p.bound do
			  if Info.ord p.heap.(i).(x)  == Info.ord p.heap.(x).(y)  then p.heap.(i).(y) <- Info.update_ord p.heap.(i).(y) (Info.ord p.heap.(x).(y));
				if Info.ord p.heap.(y).(i) ==  Info.ord p.heap.(x).(y)   then p.heap.(x).(i) <- Info.update_ord p.heap.(x).(i) (Info.ord p.heap.(x).(y));
			 done;		  
		  [p]
			end
		else
      []
end

let data_equality_variable (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x == y *)
   let x,y = index p thi lx, index p thi ly in		
   if Info.ord p.heap.(x).(y) == 0  then 
			[p]
		else
     if Info.ord p.heap.(x).(y) == 2 || Info.ord p.heap.(y).(x) == 2 then 
			[]
			else
				[p]
end

let in_equality (lx:Label.t) (ly:Label.t) p thi : t list = begin
    (* x != y *)
		let x,y = index p thi lx, index p thi ly in	
			if Info.is_equal p.heap.(x).(y) == 1 then 
			[p]
		else
      []
end

let next_var p k eq_list = begin
  let ret = ref (p.bound+10) in
	let flag = ref 0 in
  for i = 0 to p.bound do
		if !flag == 0 then begin
	   if Info.is_reach p.heap.(k).(i) == 0 then
       ret := i
		 else
		   if Info.is_equal p.heap.(k).(i) == 0 && i <> k && List.mem (i,k) !eq_list == false then
				begin
				ret := i;
				eq_list := (k,i)::!eq_list;
				flag := 1;
				end; 
		 end;
  done;		
 !ret
end

let kill_all_cutpoints p = begin
  for i =  p.bound downto p.gvar + (Array.length(p.vars)) do
		if is_cutpoint p i <> 0 then 
      begin 
			_kill p i;
      kill_cutpoints p i;
			end;
 done;
end 

let extract_from_star p k = begin
let p1 = clone p in
let p2 = clone p in
let r = next_var p k (ref []) in
p1.heap.(k).(r) <- Info.update_plus p1.heap.(k).(r);
(*Update for eualtity variable*)
for i = 0 to p1.bound do
	if Info.is_equal p1.heap.(i).(k) == 0 then begin
     for j = 0 to p1.bound do
	     if Info.is_equal p1.heap.(j).(k) == 0 then
				  p.heap.(i).(j) <- p.heap.(k).(r);
		 done;
	end;
done;
(*Second case when k and r can be equal, but only if their data is consistent*)
let new_data = intersect_data p2.data.(k).(0) p2.data.(r).(0) in
if new_data <> 5000 then begin
    p2.heap.(k).(r) <- Info.equal;
		p2.heap.(r).(k  ) <- Info.equal;
    p2.data.(k).(0) <- new_data;
	  p2.data.(r).(0) <- new_data;
    for i = 0 to p2.bound do
			if Info.is_equal p2.heap.(i).(k) == 0 then begin
			  p2.heap.(i).(r) <- Info.equal;
				p2.heap.(r).(i) <- Info.equal;
				end;
			if Info.is_reach p2.heap.(i).(k) == 0 then
				p2.heap.(i).(r) <- p2.heap.(i).(k);
				
			if Info.is_equal p2.heap.(r).(i) == 0 then begin
			  p2.heap.(k).(i) <- Info.equal;
				p2.heap.(i).(k) <- Info.equal;
				end;
			if Info.is_reach p2.heap.(r).(i) == 0 then
				p2.heap.(k).(i) <- p2.heap.(r).(i);
		done;
		
		for i = 0 to p2.bound do
		   if Info.is_equal p2.heap.(i).(k) == 0 then
				p2.data.(i).(0) <- new_data;
		done;
		
		for i = 0 to p2.bound do
		    if Info.is_equal p2.heap.(i).(k) == 0 then
					for j = 0 to p2.bound do
					   if Info.is_reach p2.heap.(j).(i) == 0 then
							p2.heap.(j).(i) <- Info.update_data_a_label p2.heap.(j).(i) new_data;
					done;
		done;
		kill_all_cutpoints p2;
end;
(p1,p2)
end

let is_star_reach p y = begin
	let ret = ref 1 in
	for i = 0 to p.bound do
		if Info.is_reach_star p.heap.(y).(i) == 0 then
			ret := 0;
	done;
	!ret
end	



let dot_next_assign' (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin
  (* x.next := y *)
  let x,y = index p thi lx, index p thi ly in
  assert( x <> y );
  p.heap.(x).(y) <- Info.dot_next_assign p.heap.(x).(y) 2;
	(*remove previous relation of x*)
	for k = 0 to p.bound do
		if Info.is_equal p.heap.(k).(x) == 0 then
	    for i = 0 to p.bound do
		    if i <> y && Info.is_reach p.heap.(k).(i) == 0 then
				  p.heap.(k).(i) <- Info.remove_path p.heap.(k).(i); 
	    done;
	done;
  (*strengthen p;*)
	(* x ->  y *)
	(* Must update for equalities constraints *)
	(* i1 -> j1*)
	(* i2 -> j2*)
	(* i3 -> j3*)
	for i = 0 to p.bound do
		for j = 0 to p.bound do
	     if Info.is_equal p.heap.(j).(y) == 0 && Info.is_equal p.heap.(i).(x) == 0 then
		    	p.heap.(i).(j) <- p.heap.(x).(y) 
		done;
	done;
  (*if p.bound < 10 then kill_all_cutpoints p;*)
	[p];   
end

let dot_next_assign (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin
	let x,y = index p thi lx, index p thi ly in
  (*if is_star_reach p x == 0 then
	begin 
		let p1,p2 = extract_from_star p x in
	  (dot_next_assign' lx ly p1 0) @ (dot_next_assign' lx ly p2 0)
	end
	else*)
		dot_next_assign' lx ly p 0
end

let dot_next_assign_dot_next (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin
  (* x.next := y.next *)
  [p];     
end  

let data_assign (lx:Label.t) (d:int) p thi : t list = begin
  (* x.data := d *)
		let x = index p thi lx in	
    p.data.(x).(0) <- d;
    for i = 0 to p.bound do
			if Info.is_equal p.heap.(i).(x) == 0 then begin
				p.data.(i).(0) <- d;
			  for j = 0 to p.bound do	
	       if Info.is_reach p.heap.(j).(i) == 0 then p.heap.(j).(i) <- Info.update_data_a_label p.heap.(j).(i) d;
			  done;
			end;
	  done;
	[p]
end

let assign_dot_next' (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin
  (* x := y.next *)
		let x,y = index p thi lx, index p thi ly in
    _kill p x;
		let c = clone p in  
		let z = ref (p.bound + 1) in
		(*Find desternitation of y and set these paths to none, it means we remove paths but keep ordring relation*)
		for i = 0 to c.bound do
        if Info.is_reach c.heap.(y).(i) == 0 && i <> x then 
					begin 
						z := i; 
					end;
		done;		
		let cell = c.heap.(y).(!z) in
		let a_label = Info.get_a_label cell in
		let b_label = Info.get_b_label cell in
		(*The first case when we can put x in between y and z*)	
    if Info.is_reach_more c.heap.(y).(!z) == 0 then 
     begin 
			 let newc1 = clone c in
			(*Find desternitation of equality node as y and set these paths to none, it means we remove paths but keep ordring relation*)
	  	for i = 0 to c.bound do
		  	if Info.is_equal c.heap.(i).(y) == 0 then
					for j = 0 to c.bound do
		  	    if Info.is_equal c.heap.(!z).(j) == 0 then c.heap.(i).(j) <- Info.remove_path c.heap.(i).(j);
	      	done;
		  done;
		  let cons = Info.unfold a_label b_label cell y !z x in				   
		  let cons_left =  fst cons in
		  let cons_right = snd cons in
			(*create configuration matrix for that*)
      let newc = clone c in
			newc.scope.(x).(0) <- newc.scope.(y).(0);
		  newc.heap.(y).(x)  <- cons_left;
		  newc.heap.(x).(!z) <- cons_right;
			(*newc.heap.(x).(!z) <- Info.update_star newc.heap.(x).(!z);*)
		  newc.data.(x).(0) <- List.nth (Info.get_a_label newc.heap.(y).(x)) 2;  
			(*Update paths of euality variables*)		
					for i = 0 to newc.bound do
					  if i <> y && (Info.is_equal newc.heap.(i).(y) == 0 || Info.is_equal newc.heap.(y).(i) == 0) then
							begin
							 newc.heap.(i).(x) <- newc.heap.(y).(x); 
							end;
					done;   
					for i = 0 to newc.bound do
					  if i <> !z && (Info.is_equal newc.heap.(i).(!z) == 0 || Info.is_equal newc.heap.(!z).(i) == 0) then
							begin
							 newc.heap.(x).(i) <- newc.heap.(x).(!z); 
							end;
					done; 
			(*Because we have new ord between x with y and z, therefore we need to saturate ord here to get all possible relation*)
			for i = 0 to newc.bound do
			  if Info.ord newc.heap.(i).(y)  == Info.ord newc.heap.(y).(x)  then newc.heap.(i).(x) <- Info.update_ord newc.heap.(i).(x) (Info.ord newc.heap.(y).(x));
				if Info.ord newc.heap.(!z).(i) == Info.ord newc.heap.(x).(!z) then newc.heap.(x).(i) <- Info.update_ord newc.heap.(x).(i) (Info.ord newc.heap.(x).(!z));
			done;		  
			(* Now for the case that x == z *)
			newc1.heap.(y).(!z) <- Info.update_reach_one newc1.heap.(y).(!z);
			(* Update for equality relation *)
			for i = 0 to newc1.bound do
			  if Info.is_equal newc1.heap.(i).(y) == 0 then
					begin
				    for j = 0 to newc1.bound do
				        if Info.is_equal newc1.heap.(j).(!z) == 0 then
									newc1.heap.(i).(j) <- newc1.heap.(y).(!z); 
			    	done;
				end;
			done;
			newc1.heap.(x).(!z) <- Info.equal;
			newc1.heap.(!z).(x) <- Info.equal;
			for i=0 to p.bound do
          if i <> x  then 
					begin
            newc1.heap.(i).(x) <- newc1.heap.(i).(!z);
            newc1.heap.(x).(i) <- newc1.heap.(!z).(i); (* diagonal *)
          end;
      done;
	    newc1.data.(x).(0)  <- newc1.data.(!z).(0);
	    newc1.scope.(x).(0) <- newc1.scope.(!z).(0);
		[newc;newc1]		 
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
	    newc.data.(x).(0) <- newc.data.(!z).(0);
	    newc.scope.(x).(0) <- newc.scope.(!z).(0);
		  [newc]
		end    
end

let assign_dot_next (lx:Label.t) (ly:Label.t) (p:t) (thi:int) : t list = begin
	let x,y = index p thi lx, index p thi ly in
  (*if is_star_reach p y == 0 then
	begin 
		let p1,p2 = extract_from_star p y in
	  (assign_dot_next' lx ly p1 0) @ (assign_dot_next' lx ly p2 0)
	end
	else*)
		assign_dot_next' lx ly p 0
end

let _assign p x y = begin
  p.heap.(x).(y)  <- Info.equal;      (* adding x = y *)
	p.heap.(y).(x)  <- Info.equal;      (* adding y = x *)
	p.data.(x).(0)  <- p.data.(y).(0);  (* adding x.data = y.data *)
	p.scope.(x).(0) <- p.scope.(y).(0); (* adding x.scope = y.scope *) 
	(* Copying y *)
  for i=0 to p.bound do
    if i <> x  then begin
      p.heap.(i).(x) <- p.heap.(i).(y);
      p.heap.(x).(i) <- p.heap.(y).(i); (* diagonal *)
    end;
  done;
end


let assign (lx:Label.t) (ly:Label.t) p thi : t list = begin
  (* x := y *)
  let x,y = index p thi lx, index p thi ly in
  _kill p x;
  _assign p x y;
  kill_all_cutpoints p;
  [p]
end

let next_mark_equality (lx:Label.t) (ly:Label.t) (d:int) p thi : t list = begin
    (* x == y *)
		let x,y = index p thi lx, index p thi ly in	
			if Info.is_reach_one p.heap.(x).(y) == 0  then 
				if p.data.(x).(0) == d 
				|| (d == 0  && (p.data.(x).(0) == 2 || p.data.(x).(0) == 3 || p.data.(x).(0) == 4 || p.data.(x).(0) == 5)) 
				|| (d == 10  && (p.data.(x).(0) == 3 || p.data.(x).(0) == 4 || p.data.(x).(0) == 5)) 
				|| (d == 11  && (p.data.(x).(0) == 2 || p.data.(x).(0) == 4 || p.data.(x).(0) == 5))  then begin
				(* update p for the success case because p may are more general then the condition due to over-approximation *)
				if Info.is_reach_more p.heap.(x).(y) == 0 then
					 	p.heap.(x).(y) <- Info.update_reach_one p.heap.(x).(y);
				p.data.(x).(0) <- d;
				(*when never a update is executed, we must to update its influence*)	
				for i = 0 to p.bound do
			    if Info.is_equal p.heap.(i).(x) == 0 then begin
				     p.data.(i).(0) <- d;
			       for j = 0 to p.bound do	
	             if Info.is_reach p.heap.(j).(i) == 0 then p.heap.(j).(i) <- Info.update_data_a_label p.heap.(j).(i) d;
			       done;
			    end;
	      done;
			  [p]
			end
		  else
			 []	
		else
      []
end

let next_mark_inequality (lx:Label.t) (ly:Label.t) (d:int) p thi  = begin
      (* x.next <> y || x.data <> d *)
		  (* It contraints two condition one if x.next <> y or x.next == y but x.data <> d *)
		  let x,y = index p thi lx, index p thi ly in		  
			if Info.is_reach_one p.heap.(x).(y) == 0  then 
				if p.data.(x).(0) <> d && ((d == 0 && p.data.(x).(0) <> 2 && p.data.(x).(0) <> 3 && p.data.(x).(0) <> 4 && p.data.(x).(0) <> 5)
				|| (d == 10  && p.data.(x).(0) <> 3 && p.data.(x).(0) <> 4 && p.data.(x).(0) <> 5) 
				|| (d == 11  && p.data.(x).(0) <> 2 && p.data.(x).(0) <> 4 && p.data.(x).(0) <> 5)) then
			   [p]
				else
				 []	
	  	else
        [p]
end

let cas_success (x:Label.t) (y:Label.t) (z:Label.t) p thi = begin
  List.fold_left (fun acc el -> (acc @ assign x z (clone el) thi)) [] (equality x y p thi)
end

let attempt_mark (x:Label.t) (y:Label.t) p thi = begin
  List.fold_left (fun acc el -> (acc @ data_assign x 11 (clone el) thi)) [] (next_mark_equality x y 0 p thi)    
end

let attempt_mark_fail (x:Label.t) (y:Label.t) p thi = begin
 next_mark_inequality x y 0 p thi  
end

let cas_success_set (x:Label.t) (y:Label.t) (d:int) (z:Label.t) p thi = begin
  List.fold_left (fun acc el -> (acc @ dot_next_assign x z (clone el) thi)) [] (next_mark_equality x y 0 p thi)   
end

let cas_fail_set (x:Label.t) (y:Label.t) (d:int) (z:Label.t) p thi = begin
  next_mark_inequality x y 0 p thi
end
  
 
  
(* No need to clone *)
let init_thread vars p thi : t list = begin
  let th = p.threads.(thi) in
  assert( th.range = 0);

  p.vars <- vars;
  let count = Array.length vars in
  let newBound = p.bound+count in
  let cut = th.lbound in (* lower bound *)
  
  let h = Array.make_matrix (newBound+1) (newBound+1) Info.none in
  let s = Array.make_matrix (newBound+1) (1) 2 in
  let d = Array.make_matrix (newBound+1) (1) 0 in
	for i=0 to p.gvar - 1 do 
	  d.(i).(0) <- p.data.(i).(0)
 done;
  	for i=0 to p.gvar - 1 do 
	  s.(i).(0) <- 0
	 done;
  for i=0 to cut - 1 do
    for j=0 to cut - 1 do (* Copy the colors and globals *) h.(i).(j) <- p.heap.(i).(j); done;
    for j=cut to p.bound do (* Taking care of the threads *) h.(i).(j+count) <- p.heap.(i).(j); done;
  done;
  
  for i=cut to p.bound do
    for j=0 to cut - 1 do h.(i+count).(j) <- p.heap.(i).(j); done;
    for j=cut to p.bound do h.(i+count).(j+count) <- p.heap.(i).(j); done;
  done;
  
  let trans = Array.make count "" in
  (* update the bounds of the thread *)
  th.range <- count;
  th.trans <- trans;
  p.bound <- newBound;
  p.heap <- h;
	p.scope <- s;
  p.data <-d;
  (* update the bounds of the other (physically after) threads *)
  for thj=thi+1 to p.nth-1 do
    let th' = p.threads.(thj) in
    th'.lbound <- th'.lbound + count;
  done;
  
  (* assign them to bottom *)
  let iBottom = index p thi Label.bottom in
  for i=cut to cut + count - 1 do
    h.(i).(i) <- Info.equal;
    _assign p i iBottom;
  done;
  [p]
end
  

  
(* No need to clone *)
let kill_thread (p:t) (thi:int) : t list = begin
  let th = p.threads.(thi) in
  let vars = th.range in
  let newBound = p.bound - vars - p.cutpoints in
  let cut = th.lbound in (* lower bound *)
  (* Removing the thread labels *)
  for i=cut to cut + vars-1 do _kill p i; done;

  let h = Array.make_matrix (newBound+1) (newBound+1) Info.none in
  (* Copying to the new heap. AFTER the label removing!! *)
  for i=0 to cut - 1 do
    for j=0 to cut - 1 do h.(i).(j) <- p.heap.(i).(j); done;
    for j=cut to newBound do h.(i).(j) <- p.heap.(i).(j+vars); done;
  done;
  for i=cut to newBound do
    for j=0 to cut - 1 do h.(i).(j) <- p.heap.(i+vars).(j); done;
    for j=cut to newBound do h.(i).(j) <- p.heap.(i+vars).(j+vars); done;
  done;
  
  p.bound <- newBound;
	p.vars <- [||];
  p.heap <- h;
  p.cutpoints <- 0;
  (* reset the thread *)
  th.pc      <- 0;
  th.promise <- Promise.NoPromise;
  th.return  <- Data.top;
  for i=0 to Array.length th.bits - 1 do th.bits.(i) <- false done;
  th.range   <- 0;
  th.trans   <- [||];
  (* update the bounds of the other (physically after) threads *)
  for thj=thi+1 to p.nth-1 do
    let th' = p.threads.(thj) in
    th'.lbound <- th'.lbound - vars;
  done;
  [p]
end

let record_insert data p thi = begin
  set_promise p thi (Promise.Insert data);
  [p]
end

(*The function is to get the next cutpoint of the variable or cutpoin at k position*)
let r p k = begin
  let res = ref [] in
  for i = 0 to p.bound do
	  if Info.is_reach p.heap.(k).(i) == 0 then
       res := i::!res;
  done;
  !res
end

(*Check if k position is leaf*)
let is_leaf p k = begin
  let ret = ref 1 in
  for i = 0 to 2 do
	if Info.is_equal p.heap.(k).(i) == 0 || Info.is_equal p.heap.(i).(k) == 0 then
		ret := 0;
	done;
  !ret
end

let get_leaf p k = begin
  let ret = ref (p.bound+1) in
  for i = 0 to 2 do
	if Info.is_equal p.heap.(k).(i) == 0 then
		ret := i;
	done;
  !ret
end

(*index of variable of thi(fist or second) matrix in intersection matrix*)				
let new_index p1 i thi =
	(*first matrix*)
	if thi == 1 then 
		i
	else
	(*second matrix*)	
	 begin
	   if i >= p1.gvar then
		    i + (Array.length p1.vars + p1.cutpoints)
	   else
		    i
	 end	
	
let get_bigest_incomming p x = begin
	  let ret = ref (0) in
   for i = (p.bound-p.cutpoints) downto 0 do
			  if (Info.is_reach p.heap.(i).(x)) == 0 then 
					ret := i;
		done;
		!ret
end

let order p cutpoints = begin
	List.sort (fun x y -> if (get_bigest_incomming p x) > (get_bigest_incomming p y) then 1 else 0) cutpoints;
end

(*To make the matrix canonical, we must to order the indices*)
let permutation p i = begin
  (*If there is no cutpoint, so we dont need to compute new index here*)
	if p.cutpoints == 0 then i 
	else 
	begin
    if i <= p.bound - p.cutpoints then i
	  else
	  	let cutpoints_list = 
			let list = ref [] in			 
      for k = p.bound - p.cutpoints + 1 to p.bound do
				  list := !list@[k]
			done;
			!list in
		  let order_cutpoints_list = order p cutpoints_list in
		  let ret = ref (p.bound +1) in
		  for k = 0 to List.length(cutpoints_list) - 1 do
			   if i == List.nth cutpoints_list k then
				  ret := List.nth order_cutpoints_list k
		  done;
      !ret
  end;
end
let order_index i p1 p2 = begin  
  let ret = ref (p2.bound + 1) in
  if i > p2.bound - p2.cutpoints then 
		begin
      let i1 = permutation p1 i in
      for k = p2.bound-p2.cutpoints + 1 to p2.bound do
         if permutation p2 k == i1 then
           ret := k
      done;
    end
   else
     ret := i;
  !ret
end 
let data_label_comp x y = begin
		match x,y with
		| 11,11 -> 0
		| 10,10 -> 0
		| 0,0 -> 0
		| 2,2 -> 0
		| 3,3 -> 0
		| 4,4 -> 0
		| 5,5 -> 0
		| 0,2 -> 0
		| 11,2 -> 0
		| 0,3 -> 0
		| 10,3 -> 0
		| 10,4 -> 0
		| 11,4 -> 0
		| 0,5 -> 0
		| 10,5 -> 0
		| 11,5 -> 0
		| _,_ -> 1
	end 
let compare_content p1 p2 thi = begin
	let org_time1  = Sys.time () in   
  if p1.cutpoints <> p2.cutpoints then
		1
  else
      if p1.bound <> p2.bound then
		1
  else
    try
			for i = 0 to p1.bound do
			    if data_label_comp p1.data.(i).(0)  p2.data.(i).(0) == 1 then raise (BreakLoop 0);
		  done;
      for i=0 to p1.bound  do 
       for j= 0 to p1.bound  do 
         if Info.compare10 p1.heap.(i).(j) p2.heap.(order_index i p1 p2).(order_index j p1 p2) <> 0 then raise (BreakLoop 0);
		   done;
      done;
		    raise (BreakLoop 1);
        with  (BreakLoop 0) -> 1
            |     
   	          (BreakLoop 1) -> 0	
end


let compare_world_0 p1 p2 = begin
  (*print_string "let compare\n";print_int p1.threads.(0).pc;print_int p2.threads.(0).pc;*)
	assert( Observer.same_state p1.observer p2.observer );
  try
		if inspect_gworld p1 p2 == 1 then 1 else
		begin		
		let th1, th2 = p1.threads.(0), p2.threads.(0) in		
    if Pervasives.compare th1.pc th2.pc == 0 then
       compare_content p1 p2 0
		else
		   1
		end	    
  with Compare i -> i	
end

let ord_data_from_path p = begin
    for i = 0 to p.bound do
			for j = 0 to p.bound do
				 if Info.is_reach p.heap.(i).(j) == 0 then
					let a_label = Info.get_a_label p.heap.(i).(j) in
					p.data.(j).(0) <- List.nth a_label 2;
					let new_ord = List.nth a_label 1 in
					let b_label = Info.get_b_label p.heap.(i).(j) in
					let is_updated = ref 0 in
					for k = 0 to (List.length b_label) -1 do
					     let elt_b_label = List.nth b_label k in
							 let ord = List.nth elt_b_label 1 in
							 if ord <> new_ord then
								 is_updated := 1;
					done; 
					if !is_updated == 0 then
							p.heap.(i).(j) <- Info.update_ord p.heap.(i).(j) new_ord;
		  done;
		done;
end
let pure_strengthen p = begin 
	 for i=0 to p.bound do
		for j=0 to p.bound do
		(*For each pair of equality matrixes*)	
    if (Info.is_equal p.heap.(i).(j)) == 0 && i <> j && i > 1 && j > 1 then 
      begin
					       
			 for k=0 to p.bound do
				 (*Update paths to i by paths to j*)
          (*ord*)
				  if (Info.is_none p.heap.(k).(i)) == 0 && k <> i && Info.ord p.heap.(k).(i) == 3 then
					p.heap.(k).(i) <- p.heap.(k).(j);
				 (*Update paths from i by paths from j*)
         if (Info.is_none p.heap.(i).(k)) == 0 && k <> j && Info.ord p.heap.(i).(k) == 3 then	
					p.heap.(i).(k) <- p.heap.(j).(k);
					
					(*reach*)
				  if (Info.is_none p.heap.(k).(i)) == 0 && k <> i && Info.is_reach p.heap.(k).(j) == 0 then
					p.heap.(k).(i) <- p.heap.(k).(j);
				 (*Update paths from i by paths from j*)
         if (Info.is_none p.heap.(i).(k)) == 0 && k <> j && Info.is_reach p.heap.(j).(k) == 0 then	
					p.heap.(i).(k) <- p.heap.(j).(k);
       done;
		end;	
	done;	
	done;
	end

let change_to_single_label label = begin
	let pointer_merge x y = begin
		match x,y with
		| 2,2 -> 2
		| 2,4 -> 4
		| 4,2 -> 4
		| 4,4 -> 4
		| 1,4 -> 4
		| 4,1 -> 4
		| 1,2 -> 4
		| 2,1 -> 4
		| 1,1 -> 1
		| _,_ -> 10
	end in
	let ord_merge x y = begin
		match x,y with
		| 2,2 -> 2
		| 2,3 -> 2
		| 3,2 -> 2
		| 3,3 -> 3
		| _,_ -> 10
	end in
	let data_merge x y = begin
		match x,y with
		| 11,0 -> 2
		| 0,11 -> 2
		| 11,11 -> 11
		| 0,0 -> 0
		| 0,2 -> 2
		| 2,0 -> 2
		| 2,2 -> 2
		| 2,11 -> 2
		| 11,2 -> 2
		| 10,0->3
		| 0,10->3
		| 0,3 -> 3
		| 3,0 -> 3
		| 10,3 -> 3
		| 3,10 -> 3
		| 3,3 -> 3
		| 10,11 -> 4
		| 11,10 -> 4
		| 4,10 -> 4
		| 10,4 -> 4
		| 4,11 -> 4
		| 11,4 -> 4
		| 4,4 -> 4
		| 3,4 -> 5
		| 4,3 -> 5
		| 2,4 -> 5
		| 4,2 -> 5
		| 2,3 -> 5
		| 3,2 -> 5
		| 5,5 -> 5
		| 3,11 -> 5
		| 11,3 -> 5
		| 4,0 -> 5
		| 0,4 -> 5
		| 2,10 -> 5
		| 10,2 -> 5
		| _,5 -> 5
		| 5, _ -> 5
		| _,_ -> 15

	end in
	if List.length label > 0 then begin
		let pointer = ref (List.nth (List.nth label 0) 0) in
		let ord     = ref (List.nth (List.nth label 0) 1) in
		let data    = ref (List.nth (List.nth label 0) 2) in
		for i = 0 to (List.length label - 1) do
		    pointer := pointer_merge (List.nth (List.nth label i) 0) !pointer;
				ord := ord_merge (List.nth (List.nth label i) 1) !ord;
				data := data_merge (List.nth (List.nth label i) 2) !data;
		done;
		[[!pointer]@[!ord]@[!data]]
		end
		else
			label
end

(*Intersection of two label*)
let rec intersect_label a b = 	
	  let map_element e1 e2 = begin
			let intersect_pointer x y = match x,y with
			| 2,2 -> 2
			| 2,4 -> 2
			| 4,2 -> 2
			| 4,4 -> 4
			| _,_ -> 1000
			in 
			let intersect_ord x y = match x,y with
			| 2,2 -> 2
			| 3,3 -> 3
			| _,_ -> 1000
			in 
				let intersect_data x y = match x,y with
			| 2,2 -> 2
			| 11,2 -> 11
			| 2,11 -> 11
			| 2,0  -> 0
			| 0,2  -> 0
			| 0,0  -> 0
			| 11,11 -> 11
			| 10,3 -> 10
			| 3,10 -> 10
			| 10,10 -> 10
			| 3,3 -> 3
			| 0,3 -> 3
			| 3,0 -> 3
			| 10,4 -> 10
			| 4,10 -> 10
			| 11,4 -> 11
			| 4,11 -> 11
			| 4,4 -> 4
			| 2,3 -> 0
			| 3,2 -> 0
			| 3,4 -> 10
			| 4,3 -> 10
			| 2,4 -> 11
			| 4,2 -> 11
			| d,5 -> d
			| 5,d -> d
			| 5,5 -> 5
			| _,_ -> 1000
			in
			let part1 = intersect_pointer (List.nth e1 0) (List.nth e2 0) in
			let part2 = intersect_ord (List.nth e1 1) (List.nth e2 1) in
			let part3 = intersect_data (List.nth e1 2) (List.nth e2 2) in
			if part1 == 1000 || part2 == 1000 || part3 == 1000 then
				[]
			else
				[part1]@[part2]@[part3]		
   end in
	  let rec _intersect x b = match b with
		| [] -> [] 
		| hd::tl -> let newhd = map_element x hd in if List.length(newhd) > 0 
		                                            then newhd::_intersect x tl else _intersect x tl in
		match a with 
		| [] -> [] 
		| hd::tl -> (_intersect hd b) @ (intersect_label tl b)

(*The fist case of matching two path when doing insersection*)
(* r(i1,i2) = r(r(i1), r(i2)) *)
let match_1 p1 p2 i1 i2 i3 = begin  
	 let r1,r2 = List.nth (r p1 i1) 0, List.nth (r p2 i2) 0 in
		(*label is b1 /\ b2 /\ a1 /\ a2 *)
		let b_label = let b_label_1 = Info.get_b_label p1.heap.(i1).(r1) in 
		              let b_label_2 = Info.get_b_label p2.heap.(i2).(r2) in 
								  intersect_label b_label_1 b_label_2 in								
									
		let a_label = let a_label_1 = Info.get_a_label p1.heap.(i1).(r1) in 
		              let a_label_2 = Info.get_a_label p2.heap.(i2).(r2) in 
									if List.length (intersect_label [a_label_1] [a_label_2]) <> 0 then
								     List.nth (intersect_label [a_label_1] [a_label_2]) 0 
									else
										[]
									in		
		if List.length(a_label) <> 0 then	
			   ((r1,r2), (a_label,b_label), (i3,r1)), true
		else
			   ((r1,r2), (a_label,b_label), (i3,r1)), false
end

(*The second case of matching two path when doing insersection*)
(* r(i1,i2) = r(r(i1), i2) *)
let match_2 p1 p2 i1 i2 i3 = begin
	  let r1,r2 = List.nth (r p1 i1) 0, i2 in
		(*label is b1 /\ b2 /\ a1 /\ a2 *)
	
		let b_label = let b_label_1 = Info.get_b_label p1.heap.(i1).(r1) in 
		              let b_label_2 = Info.get_b_label p2.heap.(i2).(List.nth (r p2 i2) 0) in 
									
								  intersect_label b_label_1 b_label_2 in
		let a_label = let a_label_1 = Info.get_a_label p1.heap.(i1).(r1) in 
	              	let b_label_2 = Info.get_b_label p2.heap.(i2).(List.nth (r p2 i2) 0) in 
									let new_b_label_2 = change_to_single_label b_label_2 in
									if List.length (intersect_label  [a_label_1] new_b_label_2) <> 0 then
		                 List.nth (intersect_label  [a_label_1] new_b_label_2) 0 
									else (*If a_label is empty*)
									begin
									  if Info.is_reach_star p1.heap.(i1).(r1) == 0 then begin 
											a_label_1
										end
									  else
										   []
									end
									in	
    if List.length(Info.get_b_label p2.heap.(i2).(List.nth (r p2 i2) 0)) == 0 then
       ((r1,r2), (a_label,b_label), (i3,r1)),false
       else
		if List.length(a_label) <> 0  then											
		     ((r1,r2), (a_label,b_label), (i3,r1)), true
		else
			   ((r1,r2), (a_label,b_label), (i3,r1)), false
end

(*The third case of matching two path when doing insersection*)
(* r(i1,i2) = r(i1, r(i2)) *)
let match_3 p1 p2 i1 i2 i3 = begin
	  let r1,r2 = i1, List.nth (r p2 i2) 0 in
		(*label is b1 /\ b2 /\ a1 /\ a2 *)
		let b_label = let b_label_1 = Info.get_b_label p1.heap.(i1).(List.nth (r p1 i1) 0) in 
		              let b_label_2 = Info.get_b_label p2.heap.(i2).(r2) in 
								  intersect_label b_label_1 b_label_2 in
		let a_label = let a_label_2 = Info.get_a_label p2.heap.(i2).(List.nth (r p2 i2) 0) in 
		              let b_label_1 = Info.get_b_label p1.heap.(i1).(List.nth (r p1 i1) 0) in 
									let new_b_label_1 = change_to_single_label b_label_1 in
									if List.length (intersect_label [a_label_2] new_b_label_1) <> 0 then List.nth (intersect_label [a_label_2] new_b_label_1) 0 
									else
                   begin
									  if Info.is_reach_star p2.heap.(i2).(List.nth (r p2 i2) 0) == 0 then
										   a_label_2
									  else
										   []
									end
									in
    if List.length(Info.get_b_label p1.heap.(i1).(List.nth (r p1 i1) 0)) == 0 then
			 ((r1,r2), (a_label,b_label), (i3,r1)),false
       else
		if List.length(a_label) <> 0	 then											
		     ((r1,r2), (a_label,b_label), (i3,r2)), true
		else   
			   ((r1,r2), (a_label,b_label), (i3,r2)), false
end


(* update matrix with a cell *)
let _update p a b x y = 
let cell = Info.create_cell a b in
p.heap.(x).(y) <- cell;
p 

(* update matrix with a cell *)
let _direct_update p a b x y = begin
let cell = Info.create_cell a b in
p.heap.(x).(y) <- cell
end

(*//////////////////////////////////////////////////////////////////Abstract Away//////////////////////////////////////////////////////////////////*)
let abstract_away p fro till p1 = begin		
   let cutpoints,p' = (_add_cutpoint p fro till) in	 
		for i = fro+1 to till do
    _mergeover p' i fro till;
	  done; 

	 (**)
   	
   let newbound = p1.bound + cutpoints in
	 (*the matrix after abstracting will be same as p1 in structure*)
   let newp = clone p1 in
   newp.threads.(0).pc <- p'.threads.(0).interf_pc;
	 let newheap = Array.make_matrix (newbound+1) (newbound+1) Info.none in
	 let newscope = Array.make_matrix (newbound+1) 1 0 in
	 let newsdata = Array.make_matrix (newbound+1) 1 0 in
	 (*Update scope  of variables*)
	

	 for i = 0 to p.bound do
		   if i <= fro then begin
       newscope.(i).(0) <- p'.scope.(i).(0); newsdata.(i).(0) <- p'.data.(i).(0);
						 end
			 else
				 if i > till then
       begin
				     newscope.(i-(till - fro)).(0) <- p'.scope.(i).(0);
			       newsdata.(i-(till - fro)).(0) <- p'.data.(i).(0); 
			end
	 done;
	 newp.bound <- newbound;
	 newp.heap <- newheap;
	 newp.scope <- newscope;
	 newp.data <-newsdata;
   newp.cutpoints <- p1.cutpoints + cutpoints;
	
  (*Update matrix*)
  for i = 0 to p'.bound do
    for j = 0 to p'.bound do
		if i <= fro then 
		 begin
		  if j <= fro then
      newp.heap.(i).(j) <- p'.heap.(i).(j)
		  else
			 if j > till then
         newp.heap.(i).(j - (till - fro)) <- p'.heap.(i).(j)
		 end
		else
		 if i > till then 
			begin
		   if j <= fro then
       newp.heap.(i- (till - fro)).(j) <- p'.heap.(i).(j)
		   else
			  if j > till then
       newp.heap.(i- (till - fro)).(j - (till - fro)) <- p'.heap.(i).(j)
		  end
    done;
  done;
  kill_all_cutpoints newp;
  newp
end
let rec local_paths p i = begin
	if  p.scope.(i).(0) == 0 then
		[i]
	else
	let output = r p i in
	  if List.length(output) > 0 then
	   i:: local_paths p (List.nth output 0)
		else
		 []
end

let remove_duplicates l =
  let open List in
  let tbl = Hashtbl.create (length l) in
  let f l e = 
    try 
      let _ = Hashtbl.find tbl e in l
    with
    | Not_found -> 
      Hashtbl.add tbl e ();
      e::l
  in
  List.rev (List.fold_left f [] l)

(*get paths from k to j*)
let get_path_label l p k j = begin
	if List.nth l k <= p.bound && List.nth l j <= p.bound then 
			begin
				 (* print_string "begin-------------------------- 1\n"; print_int k; print_int j;*)
					
	     let a_label = if List.nth l (j-1) <= p.bound then Info.get_a_label p.heap.(List.nth l (j-1)).(List.nth l j) else Info.get_a_label p.heap.(List.nth l (j-2)).(List.nth l j) in
			 (*print_string "get a_label from get_path_function"; print_int (List.nth l (j-1)); print_int (List.nth l (j)); print_int (List.length(a_label)); Info.print_label a_label;*)
		   let b_label = ref [] in
		   for t = k to j-2 do
	       let b_label_t = if List.nth l (t+1) <= p.bound then Info.get_b_label p.heap.(List.nth l t).(List.nth l (t+1)) else Info.get_b_label p.heap.(List.nth l t).(List.nth l (t+2)) in
			   let a_label_t = if List.nth l (t+1) <= p.bound then Info.get_a_label p.heap.(List.nth l t).(List.nth l (t+1)) else Info.get_a_label p.heap.(List.nth l t).(List.nth l (t+2)) in
			   let merge_a_b_t =  [a_label_t] @ b_label_t in
			   b_label := merge_a_b_t @ !b_label 
       done;
			 							(*	  print_string "end--------------------------- 1\n";*)
       let b_label_last = if List.nth l (j-1) <= p.bound then Info.get_b_label p.heap.(List.nth l (j-1)).(List.nth l j) else Info.get_b_label p.heap.(List.nth l (j-2)).(List.nth l j) in
			 b_label := remove_duplicates (b_label_last @ !b_label) ;

			 ([a_label], !b_label)
			end
	 else			
	if List.nth l k > p.bound && List.nth l j <= p.bound then 
			begin
								(*  print_string "begin-------------------------- 2\n";*)
			  if k < j - 1 then 
				  begin
	          let a_label = Info.get_a_label p.heap.(List.nth l (j-1)).(List.nth l j) in
		        let b_label = ref [] in
		        for t = k+1 to j-2 do				 
	            let b_label_t = Info.get_b_label p.heap.(List.nth l t).(List.nth l (t+1)) in
			        let a_label_t = Info.get_a_label p.heap.(List.nth l t).(List.nth l (t+1)) in
			        let merge_a_b_t =  [a_label_t] @ b_label_t in
			        b_label := merge_a_b_t @ !b_label 
            done;
            let b_label_last = Info.get_b_label p.heap.(List.nth l (j-1)).(List.nth l j) in
			      b_label := b_label_last @ !b_label;
			      let b_label_k = Info.get_b_label p.heap.(List.nth l (k-1)).(List.nth l (k+1)) in
			      let a_label_k = Info.get_a_label p.heap.(List.nth l (k-1)).(List.nth l (k+1)) in
			      let merge_a_b_k =  [a_label_k] @ b_label_k in
			      b_label := remove_duplicates (merge_a_b_k @ !b_label); 
						(* print_string "end-------------------------- 2\n";*)
            ([a_label], !b_label)
			  end
			  else
				   let a_label = Info.get_a_label p.heap.(List.nth l (k-1)).(List.nth l j) in
		       let b_label = Info.get_b_label p.heap.(List.nth l (k-1)).(List.nth l j) in
									(*  print_string "end-------------------------- 2\n";*)
           ([a_label], b_label)
		end
		else
   if List.nth l k <= p.bound && List.nth l j > p.bound then 
			begin
								 (* print_string "begin-------------------------- 3\n";*)
	     let a_label = Info.get_a_label p.heap.(List.nth l (j-1)).(List.nth l (j+1)) in
		   let b_label = ref [] in
					
		   for t = k to j-2 do
	       let b_label_t = Info.get_b_label p.heap.(List.nth l t).(List.nth l (t+1)) in
			   let a_label_t = Info.get_a_label p.heap.(List.nth l t).(List.nth l (t+1)) in
			   let merge_a_b_t =  [a_label_t] @ b_label_t in
			   b_label := merge_a_b_t @ !b_label 
       done;
       let b_label_last = Info.get_b_label p.heap.(List.nth l (j-1)).(List.nth l (j+1)) in
							 (* print_string "end-------------------------- 3\n";*)
			 b_label := remove_duplicates (b_label_last @ !b_label) ;
		   ([a_label], !b_label)
			end
		else	
	if List.nth l k > p.bound && List.nth l j > p.bound then 
		begin
							(*  print_string "begin-------------------------- 4\n";*)
	     let a_label = Info.get_a_label p.heap.(List.nth l (j-1)).(List.nth l (j+1)) in
		   let b_label = ref [] in					
		   for t = k-1 to j-2 do
	       let b_label_t = Info.get_b_label p.heap.(List.nth l t).(List.nth l (t+1)) in
			   let a_label_t = Info.get_a_label p.heap.(List.nth l t).(List.nth l (t+1)) in
			   let merge_a_b_t =  [a_label_t] @ b_label_t in
			   b_label := merge_a_b_t @ !b_label 
       done;
       let b_label_last = Info.get_b_label p.heap.(List.nth l (j-1)).(List.nth l (j+1)) in
							(*  print_string "end-------------------------- 4\n";*)
			 b_label := remove_duplicates (b_label_last @ !b_label) ;
			 ([a_label], !b_label)
	 end
	else
		([],[])
		
end

let update_cons_from_local_intersect p1 p2 l1 l2 paths = begin
	let p1' = clone p1 in
	let p2' = clone p2 in
	(*Create new cutpoints according to number of cutpoints in paths for p1 and p2*)
  for k = 0 to List.length(l1) - 1 do
	  if List.nth l1 k > p1.bound then 
			add_cutpoint p1';
		done;
		for k = 0 to List.length(l2) - 1 do
		if List.nth l2 k > p2.bound then
			add_cutpoint p2';
	done;
	for k = 0 to List.length(paths) - 2 do
		let pair_pre = List.nth paths k in
		let i1,j1 = fst pair_pre, snd pair_pre in
		let pair_succ = List.nth paths (k+1) in
		let i2,j2 = fst pair_succ, snd pair_succ in
		let (a_label_i, b_label_i) = get_path_label l1 p1 i2 i1 in
		let (a_label_j, b_label_j) = get_path_label l2 p2 j2 j1 in
		let new_a_label = intersect_label a_label_i a_label_j in
		let new_b_label = intersect_label b_label_i b_label_j in
		(*Update paths in l2 paths of p2*)
		for j = j2 to j1-1 do
			let (old_a_label,old_b_label) = get_path_label l2 p2 j (j+1) in
			if j < j1-1 then
				begin
				  let a_label = intersect_label new_b_label old_a_label in 
				  let b_label = intersect_label new_b_label old_b_label in
				  if List.length(a_label) > 0 then 
				   let cell = Info.create_cell (List.nth a_label 0) b_label in
					  (*Reset path comming from j*)
						for t = 0 to p2.bound do
							if Info.is_reach p2'.heap.(List.nth l2 j).(t) == 0 then p2'.heap.(List.nth l2 j).(t) <- Info.none;
						done;
						p2'.heap.(List.nth l2 j).(List.nth l2 (j+1)) <- cell
				end
			else
				let a_label = intersect_label new_a_label old_a_label in 
				let b_label = intersect_label new_b_label old_b_label in
				if List.length(a_label) > 0 then 
				   let cell = Info.create_cell (List.nth a_label 0) b_label in
					 	for t = 0 to p2'.bound do
							if Info.is_reach p2'.heap.(List.nth l2 j).(t) == 0 then p2'.heap.(List.nth l2 j).(t) <- Info.none;
						done;
						p2'.heap.(List.nth l2 j).(List.nth l2 (j+1)) <- cell;
		done;
		(*Update paths in l1 paths of p1*)
		p1'.heap.(List.nth l1 i2).(List.nth l1 i1) <- Info.none;
	done;
	(*print_string "\nLet see what happen with two constraints: \n";
	print_string "this is p1\n";
	print_cons p1';
	print_string "this is p2\n";
	print_cons p2';*)
	(p1', p2')
end

 let local_intersect l1 l2 p1 p2 = begin
	let leaf1, leaf2 = List.length(l1)-1, List.length(l2)-1 in
	let pairs_list = ref [[(leaf1,leaf2)]] in
	 let rec map l1 l2 pl start p1 p2 = begin
		let newstart = List.length(!pl) in
		for k = start to List.length(!pl)-1 do
			let curr = List.nth !pl k in
			let last_pair_in_curr = List.nth curr (List.length(curr)-1) in
  		let i,j = fst last_pair_in_curr, snd last_pair_in_curr in
			if i >= 1 then				
			   for j' = j-1 downto 0 do
					 let (a_label_i, b_label_i) = get_path_label l1 p1 (i-1) i in
					 let (a_label_j, b_label_j) = get_path_label l2 p2 j' j in
					 let new_a_label = intersect_label a_label_i a_label_j in
					 let new_b_label = intersect_label b_label_i b_label_j in
					 if List.length(new_a_label) > 0 then
						 if j'== j-1 then
               pl := !pl@[curr@[(i-1,j')]]
						 else
							 if List.length(new_b_label) > 0 then
								 pl := !pl@[curr@[(i-1,j')]];
							 
		     done;
		done;	
		if newstart < List.length(!pl) then
			map l1 l2 pl newstart	p1 p2
	 end in
	map l1 l2 pairs_list 0 p1 p2;
	!pairs_list
		(*	print_string "\nMapping couple are below:\n";
		for i = 0 to List.length(!pairs_list)-1 do
		let current = List.nth !pairs_list i in
    print_string "\n";
		 for j = 0 to List.length(current)-1 do
			let pair = List.nth current j in
			  print_int (List.nth l1 (fst pair)); print_int (List.nth l2 (snd pair)); print_string "  ";
		 done;
	done;*)
end

let make_up l p = begin
	let ret = ref [List.nth l (List.length l -1)] in
	for i = List.length l - 2 downto 0 do
		let path = p.heap.(List.nth l i).(List.nth l (i+1)) in
		let b_label = Info.get_b_label path in		
		if List.length b_label == 0 then
			 ret := (List.nth l i)::!ret
		else
		  let cutpoint = p.bound + 1 in (*Change it later to paramester*)
		  ret := (List.nth l i) :: cutpoint:: !ret;
	done;

		 (*  print_string "\nafter making up\n";
	  for i = 0 to List.length !ret - 1 do
		print_int (List.nth !ret i); print_string " ";
		done;*)
	  !ret
end	 

let compare_leaf p1 p2 leaf1 leaf2 = begin
	 let ret = ref 1 in
   for i = 0 to 3 do
		if Info.is_equal p1.heap.(leaf1).(i) == 0 && Info.is_equal p2.heap.(leaf2).(i) == 0 then
			ret := 0
	done;
	!ret
end

(*Extend the two configurations into one*)
let _extend p1 p2 = begin
	let bound = p1.bound + (Array.length p2.vars) + p2.cutpoints in
	let h = Array.make_matrix (bound+1) (bound+1) Info.none in
	let p = clone p1 in

	for i = 0 to bound do
		for j = 0 to bound do
			if i <= p1.bound && j <= p1.bound  then
			  if (Info.is_reach p1.heap.(i).(j) == 1 || p2.scope.(i).(0) >= 1) then
			      h.(i).(j) <-  p1.heap.(i).(j)
				else
					 	h.(i).(j) <- Info.remove_path p1.heap.(i).(j);				
			
			if i > p1.bound && j > p1.bound then 
				if ((Info.is_reach p2.heap.(i-Array.length p1.vars - p1.cutpoints).(j-Array.length p1.vars- p1.cutpoints)) == 1 || p2.scope.(i-Array.length p1.vars- p1.cutpoints).(0) >= 1) then
			      h.(i).(j) <- p2.heap.(i-Array.length p1.vars - p1.cutpoints).(j-Array.length p1.vars- p1.cutpoints)
				else
					 h.(i).(j)  <- Info.remove_path p2.heap.(i-Array.length p1.vars - p1.cutpoints).(j-Array.length p1.vars- p1.cutpoints);
			
			if i > p1.bound && j < p1.gvar then
				if ((Info.is_reach p2.heap.(i-Array.length p1.vars- p1.cutpoints).(j)) == 1) || p2.scope.(i-Array.length p1.vars- p1.cutpoints).(0) >= 1 then
			      h.(i).(j)  <- p2.heap.(i-Array.length p1.vars- p1.cutpoints).(j)
				else
					  h.(i).(j)  <- Info.remove_path p2.heap.(i-Array.length p1.vars- p1.cutpoints).(j);
			
			if i < p1.gvar && j > p1.bound then
				if ((Info.is_reach p2.heap.(i).(j-Array.length p1.vars- p1.cutpoints)) == 1 || p2.scope.(i).(0) >= 1) then
			      h.(i).(j) <- p2.heap.(i).(j-Array.length p1.vars- p1.cutpoints)
				else
					 h.(i).(j) <- Info.remove_path p2.heap.(i).(j-Array.length p1.vars- p1.cutpoints);
			
			
	  done;
	done;
	p.heap <- h;
	p.bound <- bound;
	p.vars <- Array.append p1.vars p2.vars;
	p.cutpoints <- p2.cutpoints;
	p.translation = p1.translation;
	(*Extend the scope of variables of the two configurations*)
	let scope = Array.make_matrix (bound+1) 1 0 in
	let data = Array.make_matrix (bound+1) 1 0 in
  for i = 0 to bound do
	if i <= p1.bound  then begin
	    scope.(i).(0) <- p1.scope.(i).(0); data.(i).(0) <- p1.data.(i).(0); end
	else 
		begin
		  scope.(i).(0) <- p2.scope.(i - (Array.length p1.vars) - p1.cutpoints).(0); data.(i).(0) <- p2.data.(i - (Array.length p1.vars) - p1.cutpoints).(0); 
		end;
	done;
	p.scope <- scope;
	p.data <- data;
	(*update intersection pc to pc of p2, it will be used as pc after abstraction away*)
	p.threads.(0).interf_pc <- p2.threads.(0).pc; 
	p
end





let join_cons p1 p2 = begin
  update_scope p1;
   update_scope p2; 
  let p = clone p2 in
  let terminate = ref 0 in
  if p1.bound == p2.bound && p1.cutpoints == p2.cutpoints && (p1.threads.(0).pc == p2.threads.(0).pc)  then begin
  for i = 0 to p1.bound do
    for j = 0 to p1.bound do
      if !terminate == 0 then begin
        if ((Info.is_reach p1.heap.(i).(j) == 0 && Info.is_reach p2.heap.(i).(j) == 0))
          (*&& p1.data.(i).(0) == p2.data.(i).(0) *) && p1.scope.(i).(0) == p2.scope.(i).(0) then begin 
          let a_label_1 = Info.get_a_label p1.heap.(i).(j) in
          let a_label_2 = Info.get_a_label p2.heap.(i).(j) in
          let b_label_1 = Info.get_b_label p1.heap.(i).(j) in
          let b_label_2 = Info.get_b_label p2.heap.(i).(j) in
          if (List.nth a_label_1 1) <> (List.nth a_label_2 1) then
              terminate := 1
          else
          let join_a_label = if ((List.nth a_label_1 2) + (List.nth a_label_2 2)) == 1 then
          [(List.nth a_label_1 0)] @ [(List.nth a_label_1 1)] @ [2] else
            if (List.nth a_label_1 2) == 2 then a_label_1 else if (List.nth a_label_2 2) == 2 then a_label_2 else a_label_1 in
          
          let join_b_label = remove_duplicates (b_label_1 @ b_label_2)  in
          let join_label = Info.update_label p2.heap.(i).(j) join_a_label join_b_label in
          p.heap.(i).(j) <- join_label;
          if ((List.nth a_label_1 2) + (List.nth a_label_2 2)) == 1 then
            p.data.(j).(0) <- 2 ;
        end
          else
            if ((Info.is_reach p1.heap.(i).(j) == 0 && Info.is_reach p2.heap.(i).(j) <> 0))
            then
              terminate := 1
                else
                  if ((Info.is_reach p1.heap.(i).(j) <> 0 && Info.is_reach p2.heap.(i).(j) == 0))
            then
              terminate := 1
                else
            if (Info.is_equal p1.heap.(i).(j) == 0 && Info.is_equal p2.heap.(i).(j) <> 0) || (Info.is_equal p1.heap.(i).(j) <> 0 && Info.is_equal p2.heap.(i).(j) == 0) then
           terminate := 1;
      end;   
    done;
  done;
  end
  else
    terminate := 1;
			(*cell_global_expand_local_strength_all p;*)			
  (p, !terminate)
end 

	
let next_star1 p1 p2 k1 k2 = begin
  let ret = ref (p1.bound+10) in
	let flag = ref 0 in
  for i = 0 to p1.bound do
		if !flag == 0 then begin
	   if Info.is_reach_star p1.heap.(k1).(i) == 0 then
      begin 
			 ret := i;
		   flag := 1;
			end; 
		 end;
  done;		
	if !ret == (p1.bound+10) then
		begin
			if k1 > p1.bound - p1.cutpoints && k2 <= p1.bound-p1.cutpoints && Info.is_reach p1.heap.(k1).(k2) == 0 then
		  	 ret := k2;   		
		end;
 !ret
end

let next_star2 p1 p2 k1 k2 = begin
  let ret = ref (p2.bound+10) in
	let flag = ref 0 in
  for i = 0 to p2.bound do
		if !flag == 0 then begin
	   if Info.is_reach_star p2.heap.(k2).(i) == 0 then
      begin 
			 ret := i;
		   flag := 1;
			end; 
		 end;
  done;		
	if !ret == (p2.bound+10) then
		begin
			if k2 > p2.bound - p2.cutpoints && k1 <= p2.bound-p2.cutpoints && Info.is_reach p2.heap.(k2).(k1) == 0 then
  			 ret := k1;   		
		end;
 !ret
end



let same_skeleton p1 p2 i1 i2 = begin   		
      let l = ref [] in
      let ret = ref 1 in
			let eq_list1 = ref [] in
			let eq_list2 = ref [] in
      let rec same_skeleton' p1 p2 i1 i2 = begin
		  let r1,r2 =  next_var p1 i1 eq_list1, next_var p2 i2 eq_list2 in
		  if r1 == 0 && r2 == 0 then begin l := (i1,i2)::!l;  l := (r1,r2)::!l; ret := 0 end
      else begin
        if r1 == 0 && r2 <> 0 || r1 <> 0 && r2 == 0 then  begin ret := 1; end
        else        
          if i1 <= p1.bound - p1.cutpoints && i2 <= p2.bound - p2.cutpoints && i1 <> i2 then ret := 1 
					 else 
						begin l := (i1,i2)::!l; same_skeleton' p1 p2 r1 r2; 
						if !ret == 21 && (p1.threads.(0).pc == 1013 || p1.threads.(0).pc == 13 || (p1.threads.(0).pc == 1020 ) || p1.threads.(0).pc == 20 ||  p1.threads.(0).pc == 1019) then 
							begin 						 								
						   let r1',r2' =  next_star1 p1 p2 r1 r2, next_star2 p1 p2 r1 r2 in
							 if r1' <= p1.bound && r2' > p2.bound && r1 > p1.bound - p1.cutpoints then begin 							
				              	ret := 0; 								
												l := (r1,r2)::!l;
                        same_skeleton' p1 p2 r1' r2; end;
       				 if r1' > p1.bound && r2' <= p2.bound  && r2 > p2.bound - p2.cutpoints then 
										begin 
					           	   ret := 0; 		
												l := (r1,r2)::!l;
												same_skeleton' p1 p2 r1 r2';	
									 end;
						  end;					
					end;
			end;
      end in
      same_skeleton' p1 p2 i1 i2;	
			(!l,!ret)
    end   

let same_skeleton1 p1 p2 i1 i2 = begin   
      let l = ref [] in
      let ret = ref 1 in
			let eq_list1 = ref [] in
			let eq_list2 = ref [] in
      let rec same_skeleton'1 p1 p2 i1 i2 = begin
      let r1,r2 =  next_var p1 i1 eq_list1, next_var p2 i2 eq_list2 in
        if r1 == 0 && r2 == 0 then begin l := (i1,i2)::!l;  l := (r1,r2)::!l; ret := 0 end
      else
        if r1 == 0 && r2 <> 0 || r1 <> 0 && r2 == 0 then ret := 1
        else        
          if i1 <= p1.bound - p1.cutpoints && i2 <= p2.bound - p2.cutpoints && i1 <> i2 then ret := 1 else begin l := (i1,i2)::!l;same_skeleton'1 p1 p2 r1 r2 end
      end in
      same_skeleton'1 p1 p2 i1 i2;			
      (!l,!ret)
    end   
let join_cons_full p1 p2 = begin
	update_scope p1;
	update_scope p2;
	let pointer_merge x y = begin
		match x,y with
		| 2,2 -> 2
		| 2,4 -> 4
		| 4,2 -> 4
		| 4,4 -> 4
		| 1,4 -> 4
		| 4,1 -> 4
		| 1,2 -> 4
		| 2,1 -> 4
		| 1,1 -> 1
		| _,_ -> 10
	end in
	let ord_merge x y = begin
		match x,y with
		| 2,2 -> 2
		| 2,3 -> 2
		| 3,2 -> 2
		| 3,3 -> 3
		| _,_ -> 10
	end in
		let data_merge x y = begin
		match x,y with
		| 11,0 -> 2
		| 0,11 -> 2
		| 11,11 -> 11
		| 0,0 -> 0
		| 0,2 -> 2
		| 2,0 -> 2
		| 2,2 -> 2
		| 2,11 -> 2
		| 11,2 -> 2
		| 10,0->3
		| 0,10->3
		| 0,3 -> 3
		| 3,0 -> 3
		| 10,3 -> 3
		| 3,10 -> 3
		| 3,3 -> 3
		| 10,11 -> 4
		| 11,10 -> 4
		| 4,10 -> 4
		| 10,4 -> 4
		| 4,11 -> 4
		| 11,4 -> 4
		| 4,4 -> 4
		| 3,4 -> 5
		| 4,3 -> 5
		| 2,4 -> 5
		| 4,2 -> 5
		| 2,3 -> 5
		| 3,2 -> 5
		| 5,5 -> 5
		| 3,11 -> 5
		| 11,3 -> 5
		| 4,0 -> 5
		| 0,4 -> 5
		| 2,10 -> 5
		| 10,2 -> 5
		| _,5 -> 5
		| 5, _ -> 5
		| _,_ -> 15

	end in
(*	print_string "begin \n";*) (*print_cons p1; print_cons p2;*)
	let newbound = p1.bound+p2.cutpoints in
	let newheap = Array.make_matrix (newbound+1) (newbound+1) Info.none in
	let scope =   Array.make_matrix (newbound+1) 1 0 in
	let data =    Array.make_matrix (newbound+1) 1 0 in
  for i = 0 to newbound do
	newheap.(i).(i) <- Info.equal;
	done;
	let p3 = clone p1 in
  let ret = ref 0 in
  if (p1.threads.(0).pc == p2.threads.(0).pc) && (p1.threads.(0).pc == 20 || p1.threads.(0).pc == 1020 || p1.threads.(0).pc == 1019 || p1.threads.(0).pc == 1013 || p1.threads.(0).pc == 13) then begin
  let mapping_pair, sk = same_skeleton  p1 p2 3 3 in
	let root = ref 3 in
	if sk == 0 then begin	
	for n = List.length(mapping_pair) - 1 downto 1 do
	let i1,i2 = List.nth mapping_pair n in
	let r1,r2 = List.nth mapping_pair (n-1) in 	
	let a_label_1 = Info.get_a_label p1.heap.(i1).(r1) in
  let a_label_2 = Info.get_a_label p2.heap.(i2).(r2) in
  let b_label_1 = Info.get_b_label p1.heap.(i1).(r1) in
  let b_label_2 = Info.get_b_label p2.heap.(i2).(r2) in

			
  if (List.nth a_label_1 1) <> (List.nth a_label_2 1) && (List.nth a_label_1 0) <> 1 && (List.nth a_label_2 0) <> 1 then
       begin  ret := 1;  end
   else	begin															 
          let join_a_label = [pointer_merge (List.nth a_label_1 0) (List.nth a_label_2 0)] @ [ord_merge (List.nth a_label_1 1) (List.nth a_label_2 1)] @ [data_merge (List.nth a_label_1 2) (List.nth a_label_2 2)]	in											                  
          let join_b_label = remove_duplicates (b_label_1 @ b_label_2)  in
					(*If r1 is not cutpoint ,r2 is cutpoints:*)		
						
					if r1 <= p1.bound-p1.cutpoints && r2 > p2.bound-p2.cutpoints then 
						begin 
							
							data.(r2 +p1.cutpoints).(0) <- data_merge p1.data.(r1).(0) p2.data.(r2).(0);
							newheap.(!root).(r2 +p1.cutpoints) <- Info.update_label p2.heap.(i2).(r2) join_a_label join_b_label; root := r2+p1.cutpoints; 
							if Info.is_reach p2.heap.(r1).(r2) == 0 then 
								begin 
									newheap.(r1).(r2 +p1.cutpoints) <- Info.update_star  p2.heap.(r1).(r2); data.(r1).(0) <- p2.data.(r1).(0); 
								  newheap.(r1).(r2 +p1.cutpoints) <- Info.update_data_a_label newheap.(r1).(r2 +p1.cutpoints) data.(r2+p1.cutpoints).(0);
							  end 
						 else begin 
								if Info.is_reach_star p2.heap.(r2).(r1) <> 0 && Info.is_reach p2.heap.(r2).(r1) <> 0 then 
								   begin ret := 1;   end
								else
									if Info.is_reach p2.heap.(r2).(r1) == 0 then 
								     	begin newheap.(r2 +p1.cutpoints).(r1) <- Info.update_star  newheap.(r2 +p1.cutpoints).(r1); end;
								end;
							data.(r2+p1.cutpoints).(0) <- data_merge p1.data.(r1).(0) p2.data.(r2).(0);
							
							
					  end
					else	
					   begin 
							newheap.(!root).(r1) <- Info.update_label p1.heap.(i1).(r1) join_a_label join_b_label; root := r1;	data.(r1).(0) <- data_merge p1.data.(r1).(0) p2.data.(r2).(0);
						  if r1 > p1.bound-p1.cutpoints && r2 <= p2.bound-p2.cutpoints then 
								if Info.is_reach p1.heap.(r2).(r1) == 0 then 
								begin 
									newheap.(r2).(r1) <- Info.update_star  p1.heap.(r2).(r1); 
									newheap.(r2).(r1) <- Info.update_data_a_label newheap.(r2).(r1) data.(r1).(0);
								  data.(r2).(0) <- p1.data.(r2).(0);
								end
								else
									begin
										if Info.is_reach_star p1.heap.(r1).(r2) <> 0 && Info.is_reach p1.heap.(r1).(r2) <> 0 then 
							        begin ret := 1;  end
										else
											if Info.is_reach p1.heap.(r1).(r2) == 0 && r1 > p1.bound - p1.cutpoints then 
								     	  begin newheap.(r1).(r2) <- Info.update_star  newheap.(r1).(r2); end;
					        end;  
						 end;
		end;
	done;(*Done of for mapping pair*)  
			
	end
	else ret := 1;	

	if !ret == 0 then begin
		p3.heap <- newheap;
		p3.cutpoints <- p1.cutpoints + p2.cutpoints;
		p3.bound <- newbound;
		p3.data <- data;
		p3.scope <- scope;
		(*Local joining*) 
		  
		let eq_list2 = ref [] in
					
		for i = 0 to p1.bound - p1.cutpoints do
			
			
			if p1.scope.(i).(0) == 1 && p2.scope.(i).(0) == 1 then begin
			  for k = 0 to p1.bound - 1 do
			   p3.heap.(k).(i) <- p1.heap.(k).(i);
			 done;  

				end; 
				
			if p1.scope.(i).(0) == 1 && p2.data.(i).(0) == 1 then 
				begin
				p3.data.(i).(0) <- p1.data.(i).(0);	
				p3.scope.(i).(0) <- p1.scope.(i).(0);	
					
				  
				end;
			if p1.scope.(i).(0) == 2 then begin 
				p3.scope.(i).(0) <- 2; 
			  for k = 0 to p1.bound - 1 do
			   p3.heap.(k).(i) <- p1.heap.(k).(i);
				 p3.heap.(i).(k) <- p1.heap.(i).(k);
			 done;  
			end;
			
		done;
		let eq_list1 = ref [] in
	  let eq_list2 = ref [] in
		for i = 0 to p1.bound - p1.cutpoints do
			if p1.scope.(i).(0) == 1 && p2.data.(i).(0) == 1 then 
				begin
        let r1,r2 =  next_var p1 i eq_list1, next_var p2 i eq_list2 in
				let a_label_1 = Info.get_a_label p1.heap.(i).(r1) in
        let a_label_2 = Info.get_a_label p2.heap.(i).(r2) in
        let b_label_1 = Info.get_b_label p1.heap.(i).(r1) in
        let b_label_2 = Info.get_b_label p2.heap.(i).(r2) in
				let join_a_label = [pointer_merge (List.nth a_label_1 0) (List.nth a_label_2 0)] @ [ord_merge (List.nth a_label_1 1) (List.nth a_label_2 1)] @ [data_merge (List.nth a_label_1 2) (List.nth a_label_2 2)]	in											                  
        let join_b_label = remove_duplicates (b_label_1 @ b_label_2)  in
				
				if r1 == r2 || (List.mem (r1,r2) mapping_pair) == true then 
					begin
						if List.mem (r1,r2) mapping_pair == true then
							if r1 <= p1.bound-p1.cutpoints && r2 > p2.bound-p2.cutpoints then 
							    begin
										 p3.heap.(i).(r2 +p1.cutpoints) <- Info.update_label p2.heap.(i).(r2) join_a_label join_b_label; 
										 p3.heap.(i).(r2 +p1.cutpoints) <- Info.update_data_a_label p3.heap.(i).(r2 +p1.cutpoints) data.(r2+p1.cutpoints).(0);
									end							    
					    else	
					      begin  
									p3.heap.(i).(r1) <- Info.update_label p1.heap.(i).(r1) join_a_label join_b_label;
									p3.heap.(i).(r1) <- Info.update_data_a_label p3.heap.(i).(r1) data.(r1).(0);
								end
						else
							begin
								p3.heap.(i).(r1) <- Info.update_label p1.heap.(i).(r1) join_a_label join_b_label;
								p3.heap.(i).(r1) <- Info.update_data_a_label p3.heap.(i).(r1) data.(r1).(0);
							end;
					end
					else
						ret := 1; 
				end;
		done;				
	end
	else
		ret := 1;		
			end;
		 if (p1.threads.(0).pc <> p2.threads.(0).pc) then ret := 1;
		if !ret == 0 then begin
					kill_all_cutpoints p3;							 
		end;
		(p3, !ret)
end 

let mark p i1 m = begin
  let p' = clone p in
  p'.data.(i1).(0) <- m;
	for j = 0 to p'.bound do
      if (Info.is_reach p'.heap.(j).(i1)) == 0 then
        p'.heap.(j).(i1) <- Info.update_data_a_label p'.heap.(j).(i1) m;
    done;  
  p'
end 

      
    let is_pattern p1 p2 i1 i2 = begin    
      let l = ref [] in
      let ret = ref 1 in
      let rec is_pattern' p1 p2 i1 i2 = begin
      let r1,r2 =  List.nth (r p1 i1) 0, List.nth (r p2 i2) 0 in
        if r1 == 0 && r2 == 0 then begin l := (i1,i2)::!l; ret := 0 end
      else
        if r1 == 0 && r2 <> 0 || r1 <> 0 && r2 == 0 then ret := 1
        else
        if Info.compare10 p1.heap.(i1).(r1) p2.heap.(i2).(r2) == 0 && Info.compare10 p2.heap.(i2).(r2) p1.heap.(i1).(r1) == 0 then
         begin 
           l := (i1,i2)::!l; ret := 0;is_pattern' p1 p2 r1 r2
         end
        else
          ret := 1
      end in
      is_pattern' p1 p2 i1 i2;
      (!l,!ret)
    end   
    let column_copy candidate_cons library_cons mapping_list1 mapping_list2 p1 l1 = begin
      let lib_index k mapping_list = begin
        let ret_index = ref 0 in
      for i = 0 to List.length(mapping_list)-1 do
        let candidate_index = fst (List.nth mapping_list i) in
        if k == candidate_index then
          ret_index := snd (List.nth mapping_list i); 
      done;
        !ret_index
      end in
      let bound1 = p1.bound in
      for i = 3 to candidate_cons.bound do
        for j = 0 to candidate_cons.bound do
          if i <= bound1 && j <= bound1 then begin
            if candidate_cons.scope.(i).(0) == 0 && candidate_cons.scope.(j).(0) == 0 && j <> 1 && j <> 2 then
              candidate_cons.heap.(i).(j) <- library_cons.heap.(lib_index i mapping_list1).(lib_index j mapping_list1);
          end;
          if i <= bound1 && j > bound1 then begin
            if candidate_cons.scope.(i).(0) == 0 && candidate_cons.scope.(j).(0) == 0 then
              candidate_cons.heap.(i).(j) <- library_cons.heap.(lib_index i mapping_list1).((lib_index (j-(Array.length p1.vars + p1.cutpoints)) mapping_list2)+Array.length l1.vars + l1.cutpoints);
          end;
          if i > bound1 && j <= bound1 then begin
            if candidate_cons.scope.(i).(0) == 0 && candidate_cons.scope.(j).(0) == 0 && j <> 1 && j <> 2 then
               candidate_cons.heap.(i).(j) <- library_cons.heap.((lib_index (i-(Array.length p1.vars + p1.cutpoints)) mapping_list2)+Array.length l1.vars + l1.cutpoints).(lib_index j mapping_list1);
          end;
          if i > bound1 && j > bound1 then begin
             if candidate_cons.scope.(i).(0) == 0 && candidate_cons.scope.(j).(0) == 0 then
               candidate_cons.heap.(i).(j) <- library_cons.heap.((lib_index (i-(Array.length p1.vars + p1.cutpoints)) mapping_list2)+Array.length l1.vars + l1.cutpoints).((lib_index (j-(Array.length p1.vars + p1.cutpoints)) mapping_list2)+Array.length l1.vars + l1.cutpoints);       
          end;
        done;
      done;
    end
      exception BreakLoop of int
      let is_pair_pattern p1 p2 l = begin
        let ret_list = ref [] in
        let list1,result,return_list,is_pattern_list_1,is_pattern_list_2 = ref p1,ref false,ref [],ref [],ref [] in
      try
      for i = 0 to Array.length(l)-1 do
        let l1,l2,res,ret = l.(i) in
        let (is_pattern_list1, is_pattern_ret1) = is_pattern p1 l1 3 3 in
        let (is_pattern_list2, is_pattern_ret2) = is_pattern p2 l2 3 3 in
        if is_pattern_ret1 == 0 && is_pattern_ret2 == 0  then 
            begin          
            list1 := l1;
            result := res;
            return_list := ret;
            is_pattern_list_1 := is_pattern_list1;
            is_pattern_list_2 := is_pattern_list2;
            raise (BreakLoop 1);
           end;
      done;
        raise (BreakLoop 2);
      with (BreakLoop 1) ->  if !result==true then
        begin 
          (*Copy cons to ret cons list*)
          for i = 0 to List.length(!return_list)-1 do
            let oldcons = List.nth !return_list i in
            let newcons = _extend p1 p2 in
            (*Copy for p1,p2 part*)
            column_copy newcons oldcons !is_pattern_list_1 !is_pattern_list_2 p1 !list1;    
            ret_list := newcons::!ret_list;
          done;
          (ret_list,0)
        end
      else
        (ref [],1) 
        | (BreakLoop 2) -> (ref [],1) 
      end
      


let rec intersection f p1 p2 i1 i2 i3 thi = begin
	(*Both of states are leafs and equal*)	
  if is_leaf p1 i1 == 0 && is_leaf p2 i2 == 0 && (get_leaf p1 i1) == (get_leaf p2 i2) then 
		begin
		let p =	_extend p1 p2 in
		let ret = ref [] in
			if i2 >= p2.gvar then
		     _direct_update p [1;3;0] [] i1 (i2+Array.length p1.vars + p1.cutpoints)	
		  else
			   _direct_update p [1;3;0] [] i1 i2;
		ret := p::!ret;	
		!ret,true
		end
	else
	(*One of the state is leaf but the other one is not*)
	if (is_leaf p1 i1) == 0 && (is_leaf p2 i2) == 1 then
	   [],false
	else
	if (is_leaf p2 i2) == 0 && (is_leaf p1 i1) == 1 then
	   [],false
	else		
		begin		
	(*Otherwise we need to go down and check to see what happen*)
	(*first match*)		
	let p1', res1 = begin
	let mat_1 = match_1 p1 p2 i1 i2 i3 in
	   match mat_1 with
      | _, false -> [],false (*This path is inconsistent*) 
		| mat, true -> let i1',i2',i3' =    fst ((fun (x,y,z)->x) mat),
																			  snd ((fun (x,y,z)->x) mat),
		                                    snd ((fun (x,y,z)->z) mat) in
									 let a_label, b_label =  fst ((fun (x,y,z)->y) mat), snd ((fun (x,y,z)->y) mat) in																		
   (* if (p1.data.(i1').(0) == 11 && p2.data.(i2').(0) == 0) ||  (p1.data.(i1').(0) == 0 && p2.data.(i2').(0) == 11) then 
		    [],false
    else	*)							
		match intersection f p1 p2 i1' i2' i3' 1 with 
                   | _, false -> [],false (*This path is also inconsistent*)
		               | newp, true  -> let rec update plist =  match plist with
													|  [] -> []
													|  hd::tl -> let newp1 = _update (_update hd a_label b_label (new_index p1 i3 thi) i3') [1;3;0] [] i1' (new_index p1 i2' 2 ) in 
													(_update newp1 [1;3;0] [] (new_index p1 i2' 2) i1')::update tl in
													(update newp), true
	end in 
	(*second match*)   
    let p2', res2 = begin	
      	let mat_2 = match_2 p1 p2 i1 i2 i3 in
				
	   match mat_2 with
		| _, false ->  [],false (*This path is inconsistent*) 
		| mat, true -> let i1',i2',i3' =    fst ((fun (x,y,z)->x) mat),
																			  snd ((fun (x,y,z)->x) mat),
		                                    snd ((fun (x,y,z)->z) mat) in
									 let a_label, b_label =  fst ((fun (x,y,z)->y) mat),
									                         snd ((fun (x,y,z)->y) mat) in
									
		               match intersection f p1 p2 i1' i2' i3' 1 with 
		               | _, false -> [],false (*This path is also inconsistent*)
		               | newp, true  -> let rec update plist =  match plist with
																													|  [] -> []
																													|  hd::tl -> _update hd a_label b_label (new_index p1 i3 thi) i3'::update tl in 
																						(update newp), true
	end in
	
	(*third match*)
    let p3', res3 = begin
    let mat_3 = match_3 p1 p2 i1 i2 i3 in
	   match mat_3 with
		| _, false ->  [],false (*This path is inconsistent*) 
		| mat, true -> let i1',i2',i3' = fst ((fun (x,y,z)->x) mat),
																			  snd ((fun (x,y,z)->x) mat),
		                                    snd ((fun (x,y,z)->z) mat) in
									 let a_label, b_label =  fst ((fun (x,y,z)->y) mat),
									                         snd ((fun (x,y,z)->y) mat) in
		               match intersection f p1 p2 i1' i2' i3' 2 with 
		               | _, false -> [], false (*This path is also inconsistent*)
		               | newp, true  ->  let rec update plist =  match plist with
																													|  [] -> []
																													|  hd::tl -> _update hd a_label b_label (new_index p1 i3 thi) (new_index p1 i3' 2)::update tl in
																													    
																						(update newp), true
	end in	
    let result = 	match res1, res2, res3 with
	| true,true,true ->  p1'@p2'@p3', true
	| true,false,true ->  p1'@p3', true
	| false,true,false ->  p2', true
	| true,true,false ->   p1'@p2', true
	| false,true,true ->   p2'@p3', true
	| false,false,true -> p3', true
	| false, false,false -> [], false
  | true,false,false -> p1',true in
     result
	end
end

(* =================================================================================== *)

let join ~org ~extra : bool = begin
  assert( Observer.same_state org.observer extra.observer );
  assert( org.gvar = extra.gvar );
  assert( org.colors = extra.colors );
  assert( org.nth = extra.nth );
  let changed = ref false in
  !changed
end

    
(* =================================================================================== *)

let create_queue (head:Label.t) (tail:Label.t) colors bits locks = begin
  assert( 3 = Label.unpack head && 4 = Label.unpack tail );
  let c = create ~example:Q 1 [|head;tail|] colors bits locks in
  let iNull, iHead, iTail = index c (-1) Label.nil, index c (-1) head, index c (-1) tail in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTail,iNull);(iHead,iTail)];
  _add c iHead iNull Info.reach;
  _add c iTail iNull Info.reach;
  c.heap.(iHead).(iTail) <-  Info.equal;
  c.heap.(iTail).(iHead) <-  Info.equal;
  [c]
end

let create_set (head:Label.t) (tail:Label.t) colors bits locks = begin
  assert( 3 = Label.unpack head && 4 = Label.unpack tail );
  let c = create ~example:Q 1 [|head;tail|] colors bits locks in
  let iNull, iHead, iTail = index c (-1) Label.nil, index c (-1) head, index c (-1) tail in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTail,iNull);(iHead,iTail)];
  c.heap.(iHead).(iTail) <-  Info.reach 2 2;
  c.heap.(iTail).(iHead) <-  Info.none;
	c.heap.(iTail).(0) <-  Info.reach 2 3;
  [c]
end

let create_stack (top:Label.t) colors bits locks = begin
  assert( 3 = Label.unpack top );
  let c = create ~example:Rest 2 [|top|] colors bits locks in
  let res = assign top Label.nil c (-1) in 
  res
end

let create_priority_queue_buckets (heads:Label.t array) (tails:Label.t array) colors locks = begin
  let c = create ~example:Q 2 (Array.append heads tails) colors 0 locks in
  let size = Array.length heads - 1 in
  assert( size = Array.length tails - 1 );
  let iNull = index c (-1) Label.nil in
  for i=0 to size do
    let iHead, iTail = index c (-1) heads.(i), index c (-1) tails.(i) in
    List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTail,iNull);(iHead,iTail)];
    _add c iHead iNull Info.reach;
    _add c iTail iNull Info.reach;
    c.heap.(iHead).(iTail) <-  Info.equal;
    c.heap.(iTail).(iHead) <-  Info.equal;
  done;
  [c]
end

let create_priority_queue_listbased (head:Label.t) (tailhigh:Label.t) (taillow:Label.t) colors locks = begin
  let c = create ~example:Q 2 [|head;tailhigh;taillow|] colors 0 locks in
  let iNull, iHead, iTailHigh = index c (-1) Label.nil, index c (-1) head, index c (-1) tailhigh in
  List.iter (fun (i,j) -> c.heap.(i).(j) <- Info.none; c.heap.(j).(i) <- Info.none;) [(iHead,iNull);(iTailHigh,iNull);(iHead,iTailHigh)];
  _add c iHead iNull Info.reach;
  _add c iTailHigh iNull Info.reach;
  c.heap.(iHead).(iTailHigh) <- Info.equal;
  c.heap.(iTailHigh).(iHead) <- Info.equal;
  let res = assign taillow tailhigh c (-1) in
  res
end

let _global_intersection p1 p2 = begin
	let bound = p1.bound + (Array.length p2.vars) in
	p1  
end

