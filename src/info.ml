type alpha = {ord:int;}
type beta  = {ord:int; d1:int; d2:int; d3:int*int;}
type t = {
	 r:int;                            (* it is type of relation 0 for equal, 1 for alpha and 2 for beta*alpha, 3 for none without ord and 4 for none with order*)
	 alpha: alpha;                     (* it is relation of the end point*)
	 beta:  beta;                      (* it is relation and data on the way to the end point*)
}	
(*////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)
(*  Colors: *)
(*  White: 1 *)
(*  Red:   2 *)
(*  Blue:  4 *)
(*  Red->Blue: 8 *)
(*  Blue->Red:  16 *)

(*  Looking: *)
(* 1 -> Me*)
(* 2 -> Other*)
(* 3 -> Me + Other*)
(* 4 -> Unlock*)
(* 5 -> Unlock + me*)
(* 6 -> Unlock + other*)
(* 7 -> Unlock + me + other*)                                                
(*/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////*)

(*Intersect two locks and return the intersected lock and the lock when abstract away the thread 1*)
let intersect_lock x y =match x, y with 
  | 1, 1 -> 0,0
  | 1, 2 -> 2,1
  | 1, 3 -> 2,1
  | 1, 4 -> 0,0
  | 1, 5 -> 0,0
  |	1, 6 -> 2,1
  | 1, 7 -> 2,1		
	| 2, 1 -> 1,2
	| 2, 2 -> 2,2 
	| 2, 3 -> 3,2 
	| 2, 4 -> 0,0
	| 2, 5 -> 1,2
	|	2, 6 -> 2,2
	| 2, 7 -> 3,2
	| 3, 1 -> 1,2
	| 3, 2 -> 2,3 
	| 3, 3 -> 3,3 
	| 3, 4 -> 0,0
	| 3, 5 -> 1,2
	|	3, 6 -> 2,3
	| 3, 7 -> 3,3
	| 4, 1 -> 0,0
	| 4, 2 -> 0,0
	| 4, 3 -> 0,0
	| 4, 4 -> 4,4
	| 4, 5 -> 4,4
	|	4, 6 -> 4,4
	| 4, 7 -> 4,4
	| 5, 1 -> 0,0
	| 5, 2 -> 2,1 
	| 5, 3 -> 2,1 
	| 5, 4 -> 4,4
	| 5, 5 -> 4,4
	|	5, 6 -> 6,5
	| 5, 7 -> 6,5
	| 6, 1 -> 1,2
	| 6, 2 -> 2,2 
	| 6, 3 -> 3,2 
	| 6, 4 -> 4,4
	| 6, 5 -> 5,6
	|	6, 6 -> 6,6
	| 6, 7 -> 7,6
	| 7, 1 -> 1,2
	| 7, 2 -> 2,3
	| 7, 3 -> 3,3 
	| 7, 4 -> 4,4
	| 7, 5 -> 5,6
	|	7, 6 -> 6,7
	| 7, 7 -> 7,7
	| _,_ -> 0,0
 
(*Function for colors of stack and queue*)
let compose_color x y = match x,y with
  | 1,1 -> 1     (*white + white -> white*) 
  | 1,2 -> 2     (* white + red -> red*)
  | 1,4 -> 4     (* white + blue -> blue*)
  | 1,8 -> 8     (* white + red.blue -> red.blue*)
	| 1,16 -> 16   (* while + blue.red -> blue.red*)
	| 2,1 -> 2     (* red + white -> red*)
	| 4,1 -> 4     (* blue + white -> blue*)
	| 8,1 -> 8     (* red.blue + white -> red.blue*)
	| 16,1 -> 16   (* blue.red + white -> blue.red*)
	| 2,4 -> 8     (* red + blue -> red.blue*)
	| 4,2 -> 16    (* blue + red -> blue.red*)
  | 1,32 -> 32   (*white + markedred -> markedred*)
  | 32,1 -> 32   (*markedred + white -> markedred*) 
  | 2, 2 -> 64   (*red + red -> double red*)
	| 64, 2 -> 64  (*dubred + red -> dubred*)
	| 64,64 -> 64  (*dubred + dubred -> dubred*)
	| 2, 64 -> 64  (*red + dubred -> dubred*)
	| 64,1 -> 64   (*dubred + white -> dubred*)
	| 1,64 -> 64   (*white + dubred -> dubred*)
  | _,_ -> 200   (*Something bad happen here*) 

(*Its used only for intersecting beta of match2,3*)
(*Return value is intersected color and the next color for alpha + beta intersection*)
let intersect_color x y = match x,y with
  | 1,1  ->  1,1
	| 1,2  ->  1,2
	| 1,4  ->  1,4
	| 1,8  ->  1,8
	| 1,16 ->  1,16
	| 1,32 ->  1,32
	| 2,1  ->  0, 1
	| 2,2  ->  2, 1
	| 2,4  ->  0, 4
	| 2,8  ->  2, 4
	| 2,16 ->  0, 16
	| 2,32 ->  0, 32
	| 4,1  ->  0,1
	| 4,2  ->  0,2
	| 4,8  ->  0,8
	| 4,16 ->  4,2
	| 4,32 ->  0,32
	| 4,4  ->  4, 1
	| 8,1  ->  0,1
	| 8,2  ->  0,2
	| 8,4  ->  0,4
	| 8,16 ->  0,16
	| 8,8  ->  8,1 
	| 8,32 ->  0,32 
	| 16,1  ->  0,1
	| 16,2  ->  0,2
	| 16,4  ->  0,4
	| 16,16 ->  16,1
	| 16,8  ->  0,8
	| 16,32 ->  0,32 
	| 32,1  ->  0, 1
	| 32,32  -> 32, 1
	| 32,4  ->  0, 4
	| 32,8  ->  0, 8
	| 32,16 ->  0, 16
	| 32,32 ->  32, 1
	| _,_  -> 0, 1
(*Invert the lock to the view of other threads*)
let invert_cell_lock cell = {
  r = cell.r;
  alpha = cell.alpha;
  beta = {ord = cell.beta.ord; d1 = cell.beta.d1; d2 = cell.beta.d2; d3 =  if snd cell.beta.d3 = 1 then (0, 2) else if snd cell.beta.d3 = 4 then (0, 4) else (0, fst cell.beta.d3)}	
}


let emp_alpha = {ord = 15;}
let zero_alpha = {ord = 0;}
let emp_beta = {ord = 15; d1 = 15; d2 = 15; d3 = (0,4)}

(*Interect the beta expression of two cells*)
let intersect_beta cell1 cell2 =  
	let intersect_ord = cell1.beta.ord land cell2.beta.ord in (*order must be consistent*)
	if intersect_ord = 0 then emp_beta
	else begin
	let intersect_d1 = cell1.beta.d1 land cell2.beta.d1 in    (*marked must be consistent*)
	if intersect_d1 = 0 then emp_beta
	else begin
	let intersect_d2 = cell1.beta.d2 land cell2.beta.d2 in    (*color must be equal here*)
	if intersect_d2 = 0 then emp_beta
	else begin
   let intersect_d3 = ( fst cell2.beta.d3, (snd cell1.beta.d3) land (snd cell2.beta.d3)) in (*lock must be consistent here*)
	if snd intersect_d3 = 0 then emp_beta
	else {ord = intersect_ord; d1 = intersect_d1; d2 = intersect_d2; d3 = intersect_d3}
	end			 
	end
 end
    
  let intersect_beta_elim cell1 cell2 =  
	let intersect_ord = cell1.beta.ord land cell2.beta.ord in (*order must be consistent*)
	if intersect_ord = 0 then emp_beta
	else begin
	let intersect_d1 = cell1.beta.d1 land cell2.beta.d1 in    (*marked must be consistent*)
	if intersect_d1 = 0 then emp_beta
	else begin
	let intersect_d2 =  cell1.beta.d2 land cell2.beta.d2 in    (*color must be equal here*)
	if intersect_d2 = 0 then emp_beta
	else begin
	let intersect_d3 =  (snd cell1.beta.d3) land (snd cell2.beta.d3) in (*lock must be consistent here*)
	if  intersect_d3 = 0 then emp_beta
	else {ord = intersect_ord; d1 = intersect_d1; d2 = intersect_d2; d3 = (0,intersect_d3)}
	end			 
	end
 end
  
   

  let intersect_alpha_beta_elim cell1 cell2 d1 d2 d3 = 
	let empty_ret = emp_alpha,  0, 0, (0,0) in
	let intersect_ord = cell1.alpha.ord land cell2.beta.ord in
	if intersect_ord = 220 then empty_ret else 
		begin
	      let intersect_d1 = (d1 land cell2.beta.d1) in if intersect_d1 = 0 then empty_ret else
			  let intersect_d2 = (d2 land cell2.beta.d2) in if intersect_d2 = 0 then empty_ret else 
				let intersect_d3 =  (snd d3) land (snd cell2.beta.d3) in if intersect_d3 = 0 then empty_ret else
				{ord = intersect_ord;}, intersect_d1, intersect_d2, (0,intersect_d3)			
end	
   
   

     
(*used for intersect alpha + beta and beta*)
let intersect_beta' ord cell1 cell2 =  
	let intersect_ord = cell1.beta.ord land cell2.beta.ord in (*order must be consistent*)
	if intersect_ord = 0 then emp_beta, 0, 0
	else begin
	let intersect_d1 = cell1.beta.d1 land cell2.beta.d1 in    (*marked must be consistent*)
	if intersect_d1 = 0 then emp_beta, 0, 0
	else begin
	let intersect_d2, next_color = intersect_color cell1.beta.d2 cell2.beta.d2 in    (*color must be equal here*)
	if intersect_d2 = 0 then emp_beta, 0, 0
	else begin
   let intersect_d3 = ( (if ord = 1 then fst cell2.beta.d3 else fst cell1.beta.d3), (snd cell1.beta.d3) land (snd cell2.beta.d3)) in (*lock must be consistent here*)
	if snd intersect_d3 = 0 then emp_beta, 0, 0
	else {ord = intersect_ord; d1 = intersect_d1; d2 = intersect_d2; d3 = intersect_d3}, next_color, if cell2.beta.d2 = 16 || cell2.beta.d2 = 8 then 0 else 1
	end			 
	end
  end

(*Intersect alpha expression, we care only about ord here because alpha expression do not contains color and lock as well as mark*)
let intersect_alpha cell1 cell2 = 
	let intersect_ord = cell1.alpha.ord land cell2.alpha.ord in
	if intersect_ord = 0 then
	  zero_alpha	
	else
	  {ord = intersect_ord;} 	

(*Let see how can we emmbed an alpha expression in a beta expression *)
let intersect_alpha_beta ord cell1 cell2 d1 d2 d3 = 
	let empty_ret = emp_alpha,  0, 0, (0,0), 0, 0, false in
	let intersect_ord = cell1.alpha.ord land cell2.beta.ord in
	if intersect_ord = 0 then empty_ret else 
		begin
	      let intersect_d1 = (d1 land cell2.beta.d1) in if intersect_d1 = 0 then empty_ret else 
         let intersect_d3 =  ((if ord = 1 then fst cell2.beta.d3 else fst d3), (snd d3) land (snd cell2.beta.d3)) in if snd intersect_d3 = 0 then 
        begin  empty_ret end else
				match d2, cell2.beta.d2 with
				| 1,1   (*White and White*)   -> {ord = intersect_ord;}, intersect_d1, 1(*white*),  intersect_d3, 1(*next color white*),    1,false (*the next color is also white and we can split into both star and single of the next beta expression, dont need check condition for single case*)
		    | 2,2   (*Red and Red*)       -> {ord = intersect_ord;}, intersect_d1, 2(*Red*),    intersect_d3, 1(*next color white*),    1,false (*The next color must be white and we can split*)     
        | 32,32 (*YesRed and YesRed*) -> {ord = intersect_ord;}, intersect_d1, 32(*YesRed*),intersect_d3, 1(*next color white*),    1,false (*The next color must be white and we can split*)     		      
        | 1,2   (*White and Red*)     -> {ord = intersect_ord;}, intersect_d1, 1(*White*),  intersect_d3, 2(*next color red*),      1,true  (*The next color is Red because its not taken for intersection and we can split *)
				| 4,4   (*Blue and Blue*)     -> {ord = intersect_ord;}, intersect_d1, 4(*Blue*),   intersect_d3, 1(*next color white*),    1,false (*The next color must be white and we can split*)  
				| 1,4   (*White and Blue*)    -> {ord = intersect_ord;}, intersect_d1, 1(*White*),  intersect_d3, 4(*next color blue*),     1,true  (*The next color is Blue because its not taken for intersection and we can split*)	
				| 1, 8	(*White and RedBlue*) -> {ord = intersect_ord;}, intersect_d1, 1(*White*),  intersect_d3, 8(*next color redblue*),  0,false (*The next color is Red.Blue because its not taken for intersection and we can NOT split*)
        | 1, 16 (*White and BlueRed*) -> {ord = intersect_ord;}, intersect_d1, 1(*White*),  intersect_d3, 16(*next color bluered*), 0,false (*The next color is Blue.Red because its not taken for intersection and we can NOT split*)
        | 2, 8  (*Red and RedBlue*)   -> {ord = intersect_ord;}, intersect_d1, 2(*Red*),    intersect_d3, 4(*next color blue*),     0,false (*The next color is Blue because Red is taken for intersection and we can NOT split*)
				| 4, 16 (*Blue and BlueRed*)	-> {ord = intersect_ord;}, intersect_d1, 4(*Blue*),   intersect_d3, 2(*next color red*),      0,false (*The next color is Red because Blue is taken for intersection and we can NOT split*)
				| _, _  (*Other cases*)       ->  empty_ret
end	


(*This function is used for lockfree set only*)	
let intersect_beta_alpha cell1 cell2 d1 d2 d3 = 
  let empty_ret = emp_alpha,  0, 0, (0,0), 0 in
	let intersect_ord = cell1.beta.ord land cell2.alpha.ord in
	if intersect_ord = 0 then empty_ret
	else begin
	let intersect_d1 = (d1 land cell1.beta.d1) in
   let intersect_d3 = ( 0, (snd cell1.beta.d3) land (snd d3)) in
	if intersect_d1 = 0 then empty_ret
	else if snd intersect_d3 = 0 then empty_ret
	else
		begin
		  if d2 = 1 && cell1.beta.d2 = 1      then  {ord = intersect_ord;}, intersect_d1, 1, intersect_d3, 0
	    else if d2 = 2 && cell1.beta.d2 = 2 then  {ord = intersect_ord;}, intersect_d1, 2, intersect_d3, 2
		  else if d2 = 1 && cell1.beta.d2 = 2 then  {ord = intersect_ord;}, intersect_d1, 1, intersect_d3, 1
		  else empty_ret
	  end
  end

(*Remove the color out of the cell*)
let remove_color cell = {
  r = cell.r;                         
	alpha =  cell.alpha;            
  beta  =  {ord = cell.beta.ord; d1 = cell.beta.d1; d2 = 1(*Color is back to white*); d3 = cell.beta.d3;}; (* new beta is assigned*)
}
let none =  {
	r = 3;                             (* none is encoded by 3*)
	alpha = {ord = 15;};               (* empty alpha*)
  beta  = emp_beta;                  (* empty beta*)
}
let equal =  {
  r =  0;                            (* equal is encoded by 0*)
	alpha = {ord = 1;};                (* equal relation is encoded by 1*)
  beta  = emp_beta;                  (* empty beta*)
}	

	let data_equal =  {
  r =  4;                            (* equal is encoded by 0*)
	alpha = {ord = 6;};                (* equal relation is encoded by 1*)
  beta  = emp_beta;                  (* empty beta*)
}		
let create_cell new_r new_alpha new_beta =  {
  r = new_r;                         (* new relation type*)
	alpha =  new_alpha;                (* new alpha is assigned*)
  beta  =  new_beta;                 (* new beta is assigned*)
}		
let get_none_ord cell = cell.alpha.ord				     		
let dot_next_assign new_ord  = {
	r = 1;                            (* assign relation to alpha relation*)
  alpha = {ord = new_ord;};         (* order of alpha is get from papameter*)
	beta =  emp_beta;                 (* there is no beta in this case*)
}
let update_none_ord cell new_ord = {
	r = 4;
  alpha = {ord = new_ord;};          (* new ord is updated *) 
  beta =  cell.beta;		
}	
let update_reach_one cell = {
	r = 1;
  alpha = cell.alpha;           
  beta =  emp_beta;		
}	
let update_label cell new_alpha new_beta = {
  r     = cell.r;                   (* update only alpha and beta of a relation. Therefor r is kept the same *)       
	alpha = new_alpha;                (* new alpha is assigned *)
  beta  = new_beta;				          (* new beta is assigned *)
}	
   															   
let is_none cell        =  cell.r >= 3                 
let is_none_no_ord cell =  cell.r == 3
let is_none_ord cell    =  cell.r == 4
let is_equal cell       =  cell.r == 0                  
let is_reach cell       =  cell.r == 1 || cell.r == 2    	
let is_reach_one cell   =  cell.r == 1
let is_reach_more cell  =  cell.r == 2
let get_alpha cell      =  cell.alpha
let get_alpha_ord cell  =  cell.alpha.ord
let get_beta_ord cell   =  cell.beta.ord
let get_beta cell       =  cell.beta
let get_beta_d1 cell    =  cell.beta.d1
let get_beta_d2 cell    =  cell.beta.d2
let get_beta_d3 cell    =  cell.beta.d3
let get_relation cell   =  cell.r
  
  
let print_cell cell = begin	
		  (*print b label second*)
			if cell.r == 1 || cell.r == 2 then
				 print_string "->";
			if cell.r = 2 then 
			 begin
				if cell.beta.ord = 7 then print_string ".n.";
				if cell.beta.ord = 1 then print_string ".=.";
				if cell.beta.ord = 2 then print_string ".<.";
				if cell.beta.ord = 3 then print_string ".<=.";
				if cell.beta.ord = 4 then print_string ".>.";
        if cell.beta.ord = 5 then print_string ".>=.";
        if cell.beta.ord = 6 then print_string "!=.";
				if cell.beta.d1 = 1  then print_string "No";
				if cell.beta.d1 = 2  then print_string "Yes";
				if cell.beta.d1 = 3  then print_string "YN";
			  
				if cell.beta.d1 = 4  then print_string "REM";
				if cell.beta.d1 = 8  then print_string "DAT";
				if cell.beta.d1 = 16 then print_string "INV";
				
				if cell.beta.d1 = 5  then print_string "REM-INS";
				if cell.beta.d1 = 12 then print_string "REM-DAT";
				if cell.beta.d1 = 20 then print_string "REM-INV";
				
				if cell.beta.d1 = 9  then print_string "INS-DAT";
				if cell.beta.d1 = 17 then print_string "INS-INV";

        if cell.beta.d1 = 24 then print_string "DAT-INV";
        if cell.beta.d1 = 25 then print_string "INS-INV-DAT";
        if cell.beta.d1 = 29 then print_string "INS-INV-DAT-REM";
        if cell.beta.d1 = 13 then print_string "INS-DAT-REM";
        if cell.beta.d1 = 21 then print_string "INS-INV-REM";
				
				print_string ", ";
				if cell.beta.d2 = 1     then print_string "W";
        if cell.beta.d2 = 2     then print_string "R";
        if cell.beta.d2 = 4     then print_string "B";
				if cell.beta.d2 = 8     then print_string "RB";
        if cell.beta.d2 = 16    then print_string "BR";
        if cell.beta.d2 = 32    then print_string "Rm";
				if cell.beta.d2 = 200   then print_string "BADCOLOR";
				if cell.beta.d2 = 64    then print_string "dRED";
				print_string ", ";
				if snd cell.beta.d3 = 1 then print_string "L";
				if snd cell.beta.d3 = 2 then print_string "O";
				if snd cell.beta.d3 = 3 then print_string "MO";
      if snd cell.beta.d3 = 4 then begin print_string "U"; print_string (string_of_int (fst cell.beta.d3)) end;
				if snd cell.beta.d3 = 5 then print_string "MU";
				if snd cell.beta.d3 = 6 then print_string "OU";
      if snd cell.beta.d3 = 7 then print_string "MOU";
      if snd cell.beta.d3 = 15 then print_string "UNKOWN";
			  print_string "| ->";			
				if cell.alpha.ord = 7   then print_string ".n.";
				if cell.alpha.ord = 1   then print_string ".=.";
				if cell.alpha.ord = 2   then print_string ".<.";
				if cell.alpha.ord = 3   then print_string ".<=.";
				if cell.alpha.ord = 4   then print_string ".>.";
        if cell.alpha.ord = 5   then print_string ".>=.";
        if cell.alpha.ord = 6   then print_string "!=.";
			 end			
			else			
			(*print a label secondly*)
       if cell.r <> 3 then 
			 begin
				if cell.alpha.ord = 7 then print_string ".n.";
				if cell.alpha.ord = 1 then print_string ".=.";
				if cell.alpha.ord = 2 then print_string ".<.";
				if cell.alpha.ord = 3 then print_string ".<=.";
				if cell.alpha.ord = 4 then print_string ".>.";
				if cell.alpha.ord = 5 then print_string ".>=.";
				if cell.alpha.ord = 6 then print_string ".==.";
			 end
	    else
			if cell.r == 3 then print_string ".n";
	
end

(*Merge two cells and return the result including merged cell and flag showing its possible to merge or not*)
let merge_cell cell1 cell2 =	 
  if cell1.r = cell2.r then 
	begin
	   let res = ref true in
	   if cell1.r = 1 then (*Single pointer is just needed to merge order*)
			begin 
		    let alpha_ord = cell1.alpha.ord lor cell2.alpha.ord in
         if alpha_ord = 0 then res := false;
	      let merge_alpha = {ord = alpha_ord;} in	 	 	
	      let t = {r = cell1.r; alpha = merge_alpha; beta = cell1.beta} in
	      t,!res
       end    
	   else begin          (*plus pointer is needed to merge beta and order*)
        let alpha_ord   = cell1.alpha.ord lor cell2.alpha.ord in
	      let merge_alpha = {ord = alpha_ord;} in
	      let beta_ord    =  cell1.beta.ord lor cell2.beta.ord in
	      let beta_d1     = cell1.beta.d1 lor cell2.beta.d1 in (*Marked Fields*)
      let beta_d2     = cell1.beta.d2 in
     let beta_d3 = (fst cell1.beta.d3, snd cell1.beta.d3 lor snd cell2.beta.d3) in
      if cell1.beta.d2 <> cell2.beta.d2 || alpha_ord = 0  then res := false; (*We do not merge when color fields are different*)
	      let merge_beta = {ord = beta_ord; d1 = beta_d1; d2 = beta_d2; d3 = beta_d3} in	 	
        let t = {r = cell1.r; alpha = merge_alpha; beta = merge_beta} in
	      t,!res
	   end
   end
 else
	   none, false

let compare_cell cell1 cell2 = 
 if cell1.r = cell2.r && cell1.alpha.ord land cell2.alpha.ord = cell1.alpha.ord 
	   && cell1.beta.ord land cell2.beta.ord = cell1.beta.ord && cell1.beta.d1 land cell2.beta.d1 = cell1.beta.d1 
		 && cell2.beta.d2 = cell1.beta.d2  && snd cell1.beta.d3 land  snd cell2.beta.d3 = snd cell1.beta.d3 then
		 true
	else
		 false
		
let unfold_single_cell cell = begin
	let l_cell = cell in
	let r_cell = equal in
  (l_cell, r_cell)							 	
end	

let unfold_plus cell = begin
  let l_cell = {r = 1; alpha = {ord = cell.beta.ord;}; beta = emp_beta;} in
	let r_cell = cell in	
	let r_cell1 = {r = 1; alpha = cell.alpha; beta = emp_beta;} in
		(l_cell, r_cell),(l_cell, r_cell1)					 	
end	

let prev_unfold_single_cell cell = begin
	let l_cell = equal in
	let r_cell = cell in
  (l_cell, r_cell)							 	
end	

let prev_unfold_plus cell = begin
  let l_cell = cell in
	let r_cell =  {r = 1; alpha = {ord = cell.alpha.ord;}; beta = emp_beta;}  in	
	let l_cell1 = {r = 1; alpha = {ord = cell.beta.ord;};  beta = emp_beta;}  in	
	(*plus, single*)(l_cell, r_cell),(*single, single*)(l_cell1, r_cell)					 	
end	

let compose_two_cells cell1 cell2 d1 d2 d3 = 
{
  r = 2;	
  beta = if cell1.r = 2 && cell2.r = 2 then 
	      {
	        ord = cell1.beta.ord lor cell1.alpha.ord lor cell2.beta.ord;
				  d1  = cell1.beta.d1  lor d1 lor cell2.beta.d1; 
				  d2  = compose_color cell1.beta.d2 (compose_color d2 cell2.beta.d2); 
					d3  = (0, (snd cell1.beta.d3 lor snd d3 lor  snd cell2.beta.d3)); 
				}
				else if cell1.r = 2 && cell2.r = 1 then
				{
	        ord = cell1.beta.ord lor cell1.alpha.ord;
				  d1  = cell1.beta.d1  lor d1; 
				  d2  = compose_color cell1.beta.d2 d2; 
					d3  = ( 0, snd cell1.beta.d3  lor snd d3); 
				}
				else if cell1.r = 1 && cell2.r = 1 then	
				{
	        ord = cell1.alpha.ord;
				  d1  = d1; 
				  d2  = d2; 
					d3 = d3;
				}
				else if cell1.r = 1 && cell2.r = 2 then 
	      {
	        ord = cell1.alpha.ord lor cell2.beta.ord;
				  d1  =  d1 lor cell2.beta.d1; 
				  d2  =  compose_color d2  cell2.beta.d2; 
					d3  =  (0, snd d3 lor snd cell2.beta.d3); 
				}
				else  emp_beta;	
  alpha = cell2.alpha;
}

let reach_hw_q =  {
	r = 2;                              (* none is encoded by 3*)
	alpha = {ord = 15;};                (* empty alpha*)
  beta  = {ord = 15; d1 = 1; d2 = 1; d3 = (0,4)};  (* empty beta*)
}	  

let reach_local =  {
	r = 2;                              (* none is encoded by 3*)
	alpha = {ord = 2;};                (* empty alpha*)
  beta  = {ord = 2; d1 = 2; d2 = 1; d3 = (0,4)};  (* empty beta*)
}	  
					let reach_unordered =  {
	r = 1;                              (* none is encoded by 3*)
	alpha = {ord = 16;};                (* empty alpha*)
                    beta  = emp_beta(*{ord = 16; d1 = 16; d2 = 1; d3 = (0,4)}*);  (* empty beta*)
}	
                         
    

let is_reach1 cell = (cell.r == 1 )&& (cell.alpha.ord == 2)
let is_reach2 cell = (cell.r == 1 )&& (cell.alpha.ord == 16)
let is_reach_a cell = (cell.r == 1 )&& (cell.alpha.ord == 17)
let is_reach_c cell = (cell.r == 1 )&& (cell.alpha.ord == 18)

let reach_q =  {
	r = 1;                              (* none is encoded by 3*)
	alpha = {ord = 16;};                (* empty alpha*)
    beta  = emp_beta;                   (* empty beta*)
}
    
    
    		  
let reach_a =  {
	r = 1;                              (* none is encoded by 3*)
	alpha = {ord = 17;};                (* empty alpha*)
  beta  = emp_beta;                   (* empty beta*)
               }
    
    let reach_c =  {
	r = 1;                              (* none is encoded by 3*)
	alpha = {ord = 18;};                (* empty alpha*)
  beta  = emp_beta;                   (* empty beta*)
}
                      
    
let reach_equal =  {
	r = 1;                              (* none is encoded by 3*)
	alpha = {ord = 4;};                (* empty alpha*)
    beta  = emp_beta;                   (* empty beta*)
}				
							       
let reach1 =  {
	r = 1;                              (* none is encoded by 3*)
	alpha = {ord = 2;};                 (* empty alpha*)
  beta  = emp_beta;                   (* empty beta*)
}

let reach2 =  {
	r = 1;                              (* none is encoded by 3*)
	alpha = {ord = 2;};                (* empty alpha*)
  beta  = emp_beta;                   (* empty beta*)
}
let reach_unordered =  {
	r = 1;                              (* none is encoded by 3*)
	alpha = {ord = 16;};                 (* empty alpha*)
  beta  = emp_beta;                   (* empty beta*)
}
let reach2 =  {
	r = 1;                              (* none is encoded by 3*)
	alpha = {ord = 16;};                (* empty alpha*)
  beta  = emp_beta;                   (* empty beta*)
}
let reach_multi_set =  {
	r = 2;                              (* none is encoded by 3*)
	alpha = {ord = 6;};                 (* empty alpha*)
 beta  = {ord = 16; d1 = 1; d2 = 1; d3 = (0,4)};  (* empty beta*)
}
let reach_inv =  {
	r = 2;                              (* none is encoded by 3*)
	alpha = {ord = 16;};                (* empty alpha*)
    beta  = {ord = 16; d1 = 16; d2 = 1; d3 = (0,4)};  (* empty beta*)
}	
let reach3 =  {
	r = 2;                              (* none is encoded by 3*)
	alpha = {ord = 2;};                 (* empty alpha*)
  beta  = {ord = 2; d1 = 3; d2 = 15; d3 = (0,4)}; (* empty beta*)
}
 
let assign_color cell color = {
  r = cell.r;                         (* new relation type*)
	alpha =  cell.alpha;                (* new alpha is assigned*)
  beta  =  {ord = cell.beta.ord; d1 = cell.beta.d1; d2 = color; d3 = cell.beta.d3;}; (* new beta is assigned*)
}