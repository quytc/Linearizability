(* ========================================================================================================= *)
(* =====================                  Predicate Transformer                     ======================== *)
(* ========================================================================================================= *)
let sprintf = Printf.sprintf

let debug = false
let pause = false
module C = Constraint
type cons = C.t
type help = C.help
  (** The concrete type of a transformer. *)
class type transformer =
  object
    method post: cons -> int -> cons list
    method post_interf: cons -> int -> cons list
    method strengthen: cons -> int -> cons list
    method filter: cons -> int -> cons list   
    method is_interf:  bool
		method is_interfed: bool
    method toString: string
    method fromPC: int
    method toPC: int
  end

type t = transformer
      
let post r c = begin
				
  let nth = C.nthreads c in
  let rec post_rec thi acc =
	if (C.pc c thi) = r#fromPC then begin
	try match r#post c thi with
	| [] -> acc
	| all ->
	    let finals = List.fold_left (fun accu p -> begin
	      C.set_pc p thi r#toPC;
	      C.set_in_queue p false;
	      [p] @ accu
	    end) acc all
	    in
	    finals
	with C.IgnoreConstraint -> 
	  acc
      end else acc
  in  post_rec 0 []
				
end
  
    
let strengthen r c = begin
		 let rec strengthen_rec thi acc =
    if (C.pc c thi) = r#fromPC then begin
	try match r#strengthen c thi with
	| [] -> acc
	| all ->
	    let finals = List.fold_left (fun accu p -> begin
				 C.set_pc p thi r#fromPC;
	      [p] @ accu
	    end) acc all
	    in
	    finals
	with C.IgnoreConstraint -> 
	  acc
      end else acc
  in  strengthen_rec 0 []	
					
end
  
let filter r c = begin
		 let rec filter_rec thi acc =
    if (C.pc c thi) = r#fromPC then begin
	try match r#filter c thi with
	| [] -> acc
	| all ->
	    let finals = List.fold_left (fun accu p -> begin
				 C.set_pc p thi r#fromPC;
	      [p] @ accu
	    end) acc all
	    in
	    finals
	with C.IgnoreConstraint -> 
	  acc
      end else acc
  in  filter_rec 0 []	
					
end
  
let post_interf r c  = begin
			
  			
  let nth = C.nthreads c in
  let rec post_rec thi acc =
  (*  if thi = nth then acc else begin
      post_rec (thi+1) 
	*)			
				
	if (C.pc c thi) = r#fromPC then begin
	try match r#post_interf c thi with
	| [] -> acc
	| all ->
	    let finals = List.fold_left (fun accu p -> begin
	      C.set_pc p thi r#toPC;
	      C.set_in_queue p false;
	      [p] @ accu
	    end) acc all
	    in
	    finals
	with C.IgnoreConstraint -> 
	  acc
      end else acc
  in  post_rec 0 []
				
end

let is_interf r =  r#is_interf
let name r =  r#toString
let is_interfed r =  r#is_interfed

(* ============================ Transformer implementation ======================================== *)



class assign (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.assign x y (C.clone p)
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf =  not(Label.is_local x) 
    method is_interfed =  (Label.is_global x) || (Label.is_global y) 
   method post_interf = this#post
  end

class nothing (fromPC:int) (toPC:int)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = "nothing"
    method post (p:C.t) = C.nothing (C.clone p)
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = false
		method is_interfed = false
   method post_interf = this#post
  end

class data_exchange (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.data_exchange x y (C.clone p)
    method strengthen (p:C.t) = C.hq_deq_strengthen y (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = false
		method is_interfed = false
    method post_interf = this#post
  end


class reach (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.reach x y (C.clone p)
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
		method is_interfed = true
   method post_interf = this#post
  end


class unreach (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.unreach x y (C.clone p)
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
		method is_interfed = true
   method post_interf = this#post
  end


class reach_one (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.reach_one x y (C.clone p)
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = false
		method is_interfed = false
   method post_interf = this#post
  end

class dot_next_assign (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.dot_next_assign x y (C.clone p)
    method is_interf  = true
    method is_interfed = (Label.is_global y)
    method strengthen = C.strengthen_dot_next_assign x y
    method filter = C.nothing
    method post_interf = this#post
  end

class dot_next_assign_alone (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.dot_next_assign_alone x y (C.clone p)
    method is_interf  = true
    method is_interfed = (Label.is_global y)
    method strengthen =C.nothing
    method filter = C.nothing
    method post_interf = this#post
  end
class color_var_inequality (fromPC:int) (toPC:int)  (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.color_var_equality x y (C.clone p)
    method is_interf = true
      method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class color_var_equality (fromPC:int) (toPC:int)  (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.color_var_equality x y (C.clone p)
    method is_interf = true
      method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
class data_assign_unordered (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.data_assign x d (C.clone p)
    method is_interf = true
    method is_interfed = false
    method strengthen (p:C.t) =C.strengthen_data_assign_unordered x (C.clone p)
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
class dot_next_assign_local (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.dot_next_assign x y (C.clone p)
    method is_interf  = false
    method is_interfed = (Label.is_global y)
    method strengthen =C.nothing
    method filter = C.nothing
    method post_interf = this#post
  end


class data_assign (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.data_assign x d (C.clone p)
    method is_interf = true
		method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class op_assign (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.op_assign x d (C.clone p)
    method is_interf = true
	method is_interfed = true
    method strengthen (p:C.t) =C.nothing (C.clone p)
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class elim_data_assign (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.elim_data_assign x y (C.clone p)
    method is_interf = true
	method is_interfed = true
    method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class get_him_success (fromPC:int) (toPC:int) (lq:Label.t) (lh:Label.t) (lp:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.get_him_success lq lh lp (C.clone p)
    method is_interf = false
      method is_interfed = true
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

	class get_him_fail (fromPC:int) (toPC:int) (lq:Label.t) (lh:Label.t) (lp:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.get_him_fail lq lh lp (C.clone p)
    method is_interf = false
      method is_interfed = false
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class cas_data_elim_fail (fromPC:int) (toPC:int) (x:Label.t) (d1:int) (d2:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_data_elim_fail x d1 d2
    method strengthen =  C.nothing 
      method filter= C.nothing 
      method is_interf = false
      method is_interfed = true
    method post_interf = this#post
  end

class cas_data_fail (fromPC:int) (toPC:int) (x:Label.t) (d1:int) (d2:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_data_fail x d1 d2
    method strengthen =  C.nothing 
      method filter= C.nothing
      method is_interf = false
      method is_interfed = true
    method post_interf = this#post
  end


class cas_data_elim_success (fromPC:int) (toPC:int) (x:Label.t) (d1:int) (d2:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_data_elim_success x d1 d2
    method strengthen =  C.strengthen_cas_data_elim_success x d1 d2 
      method filter= C.nothing
         method is_interf = true
      method is_interfed = true
    method post_interf = this#post
  end

class op_equality (fromPC:int) (toPC:int)  (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.op_equality x d (C.clone p)
    method is_interf = false
    method is_interfed = false  
    method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class op_inequality (fromPC:int) (toPC:int)  (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.op_inequality x d (C.clone p)
    method is_interf = false
    method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class var_data_assign (fromPC:int) (toPC:int) (s:Label.t) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.var_data_assign s x (C.clone p)
    method is_interf = false
		method is_interfed = true
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
	
class kill_variable (fromPC:int) (toPC:int)  (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.kill_variable x (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
	
class color_assign (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.color_assign x d (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class color_assign_variable (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.color_assign_variable x y (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	


class data_equality (fromPC:int) (toPC:int)  (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.data_equality x d (C.clone p)
    method is_interf = false
    method is_interfed = true
    method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
	
class color_equality (fromPC:int) (toPC:int)  (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.color_equality x d (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
	

class is_color_equality (fromPC:int) (toPC:int)  (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.is_color_equality x d (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
			
class color_inequality (fromPC:int) (toPC:int)  (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.color_inequality x d (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing  (C.clone p)
    method post_interf = this#post
  end
class hq_unnull_node (fromPC:int) (toPC:int)  (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.hq_unnull_node x (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class hq_null_node (fromPC:int) (toPC:int)  (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.hq_null_node x (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen (p:C.t) =C.nothing (C.clone p)
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

	class get_marked_assign_dot_next (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (marked:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.get_marked_assign_dot_next x y marked 
    method is_interf = not(Label.is_local x)
		method is_interfed = true
		method strengthen = C.nothing
    method filter = C.nothing 
   method post_interf = this#post
  end

class var_equality (fromPC:int) (toPC:int) (lmark:Label.t) (d:int)   =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post(p:C.t) = C.var_equality lmark d (C.clone p) 
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
	
class var_inequality (fromPC:int) (toPC:int) (lmark:Label.t) (d:int)   =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post(p:C.t) = C.var_inequality lmark d (C.clone p) 
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
	
class data_inequality (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.data_inequality x d (C.clone p)
    method is_interf = false
    method is_interfed = true
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class validate_push (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_push x (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class validate_ex_enqueue_dequeue (fromPC:int) (toPC:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = C.validate_ex_enqueue_dequeue
  end	



class validate_pop (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_pop x (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

	class validate_pop_empty (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_pop_empty x (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
	
class validate_enqueue (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_enqueue x (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class validate_call_enqueue (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_call_enqueue x (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class validate_ret_enqueue (fromPC:int) (toPC:int) (x:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_ret_enqueue x (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class validate_ret_dequeue (fromPC:int) (toPC:int) (x:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_ret_dequeue x (C.clone p)
    method is_interf = true
		method is_interfed = false
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
	
class validate_dequeue (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_dequeue x (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
	
	
class validate_dequeue_empty (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_dequeue_empty x (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

(*	

class validate_insert (fromPC:int) (toPC:int) (x:Label.t) (pcs: int list) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_insert x pcs ret (C.clone p) 
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
*)
class validate_insert_unordered (fromPC:int) (toPC:int) (x:Label.t) (pcs: int list) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_insert_unordered x pcs ret (C.clone p) 
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class validate_return (fromPC:int) (toPC:int) (x:int) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_return x ret (C.clone p) 
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class validate_return_new (fromPC:int) (toPC:int) (x:int) (lv:Label.t) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_return_new x lv ret (C.clone p) 
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	


class validate_uninsert (fromPC:int) (toPC:int) (x:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_uninsert x (C.clone p) 
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
class validate_undelete (fromPC:int) (toPC:int) (x:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_undelete x (C.clone p) 
    method is_interf = false
		method is_interfed = true
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end


class validate_fixed_uninsert (fromPC:int) (toPC:int) (x:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_fixed_uninsert x (C.clone p) 
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
class validate_fixed_undelete (fromPC:int) (toPC:int) (x:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_fixed_undelete x (C.clone p) 
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end


(*
class validate_delete (fromPC:int) (toPC:int) (x:Label.t) (pcs: int list) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_delete x pcs ret (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen =  C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
*)

class validate_delete_unordered (fromPC:int) (toPC:int) (x:Label.t) (pcs: int list) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_delete_unordered x pcs ret (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen =  C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class validate_delete (fromPC:int) (toPC:int) (x:Label.t) (b:bool) (h:help list) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_delete x b h (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class validate_insert (fromPC:int) (toPC:int) (x:Label.t) (b:bool) (h:help list) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_insert x b h (C.clone p)
    method is_interf = true
		method is_interfed = true
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
class validate_early_contains (fromPC:int) (toPC:int) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_early_contains ret (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
class validate_contains (fromPC:int) (toPC:int) (lx:Label.t) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_contains lx ret (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end		


class validate_contains_local (fromPC:int) (toPC:int) (lx:Label.t) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_contains_local lx ret (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class validate_ccas (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_ccas x y (C.clone p) 
    method is_interf = false
		method is_interfed = false
    method strengthen =C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class validate_unsuccess_ccas (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_unsuccess_ccas x y (C.clone p) 
    method is_interf = false
      method is_interfed = false
    method strengthen =C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end


class validate_help_ccas (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.nothing 
    method is_interf = false
      method is_interfed = false
    method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf (p:C.t) = C.validate_help_ccas x y (C.clone p) 
  end

	
class ccas_success (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) (r:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.ccas_success x y z r
    method strengthen = C.nothing
    method filter = C.nothing
    method is_interf = true
      method is_interfed = true
    method post_interf = this#post
  end

class ccas_fail (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) (r:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.ccas_fail x y z r
    method strengthen = C.nothing
    method filter = C.nothing
    method is_interf = true
      method is_interfed = true
    method post_interf = this#post
  end

class ccas_success_new (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.ccas_success_new x y 
    method strengthen = C.nothing
    method filter = C.nothing
    method is_interf = true
      method is_interfed = true
    method post_interf = this#post
  end	

class ccas_success_old (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.ccas_success_old x y 
    method strengthen = C.nothing
    method filter = C.nothing
    method is_interf = true
      method is_interfed = true
    method post_interf = this#post
  end	

class ccas_help_success_new (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.nothing
    method strengthen = C.nothing
    method filter = C.nothing
    method is_interf = true
      method is_interfed = true
    method post_interf = C.ccas_help_success_new x y 
  end	

class ccas_help_success_old (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.nothing
    method strengthen = C.nothing
    method filter = C.nothing
    method is_interf = true
      method is_interfed = true
    method post_interf = C.ccas_success_old x y 
  end	
												
																																				
class create_desc (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.create_desc x y z 
    method strengthen = C.nothing
    method filter = C.nothing
    method is_interf = false
      method is_interfed = false
    method post_interf = this#post
  end	

class create_desc_rdcss (fromPC:int) (toPC:int) (ld:Label.t) (la:Label.t) (lo:Label.t) (ln:Label.t) (lc:Label.t) (le:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.create_desc_rdcss ld la lo ln lc le 
    method strengthen = C.nothing
    method filter = C.nothing
    method is_interf = false
      method is_interfed = false
    method post_interf = this#post
  end	




	
										
	
class validate_contains_new (fromPC:int) (toPC:int) (v:Label.t) (ret: bool) (h:help list) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_contains_new v ret h (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end		

class validate_contains_alone_new (fromPC:int) (toPC:int) (v:Label.t) (ret: bool) (h:help list) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_contains_alone_new v ret h (C.clone p)
    method is_interf = false
		method is_interfed = true
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
	
	
	class validate_contains_alone_true (fromPC:int) (toPC:int) (v:Label.t) (ret: bool) (h:help list) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_contains_alone_true v ret h (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
	
	
class validate_fixed_contains (fromPC:int) (toPC:int) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_fixed_contains ret (C.clone p)
    method is_interf = false
	method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class set_flag (fromPC:int) (toPC:int) (op:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.set_flag (C.clone p) op
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	

class kill_flag (fromPC:int) (toPC:int)=
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.kill_flag (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
class kill_ret (fromPC:int) (toPC:int)=
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.kill_ret (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end	
class validate_contains_alone (fromPC:int) (toPC:int) (ret: bool) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_contains_alone ret (C.clone p)
    method is_interf = false
		method is_interfed = true
    method strengthen =C.empty
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end		

class red_seen (fromPC:int) (toPC:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.red_seen (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen =this#post
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class red_not_seen (fromPC:int) (toPC:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.red_not_seen (C.clone p)
    method is_interf = false
		method is_interfed = false
    method strengthen =this#post
      method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class data_inequality_variable (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.data_inequality_variable x y (C.clone p)
    method is_interf = false
		method is_interfed = false
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class data_assign_variable (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.data_assign_variable x y (C.clone p)
    method is_interf = false
		method is_interfed = false
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class data_equality_variable (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.data_equality_variable x y (C.clone p)
    method is_interf = false
		method is_interfed = false
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class assign_self_dot_next (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.assign_self_dot_next x (C.clone p)
    method is_interf = not(Label.is_local x);
		method is_interfed = not(Label.is_local x);
		method strengthen =C.nothing
    method filter = C.nothing 
    method post_interf = this#post
  end

class assign_dot_next (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.assign_dot_next x y (C.clone p)
    method is_interf = not(Label.is_local x);
	method is_interfed = true;
	method strengthen = C.nothing
    method filter = C.nothing 
    method post_interf = this#post
  end
	
	
class assign_dot_next_prev (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.assign_dot_next_prev x y (C.clone p)
    method is_interf = false
		method is_interfed = true
    method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
(* local label only *)
class new_cell (fromPC:int) (toPC:int) ?(gc=false) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) thi = C.make_new_cell x (C.clone p) thi
    method is_interf = false
		method is_interfed = false
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class global_lock (fromPC:int) (toPC:int)  (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) thi = C.global_lock x (C.clone p) thi
    method is_interf = false
		method is_interfed = false
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class global_unlock (fromPC:int) (toPC:int)  (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) thi = C.global_unlock x (C.clone p) thi
    method is_interf = false
		method is_interfed = false
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
class next_equality (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.next_equality x y
    method is_interf = false
		method is_interfed = true
		method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class next_inequality (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.next_inequality x y
    method is_interf = false
		method is_interfed = true
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end
		
class equality (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.equality x y
    method is_interf = false
		method is_interfed = false
		method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class less_than (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.less_than x y
    method is_interf = false
		method is_interfed = false
		method strengthen =C.nothing
    method filter = C.nothing  
    method post_interf = this#post
  end	


class equal (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.equal x y
    method is_interf = false
		method is_interfed = false
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class in_equal (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.in_equal x y
    method is_interf = false
		method is_interfed = false
		method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method post_interf = this#post
  end

class equal_red (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.equal_red x
    method is_interf = false
	method is_interfed = false
	method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
 method post_interf = this#post
  end	

class canbe_red (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.canbe_red x y z
    method is_interf = false
	method is_interfed = false
	method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
 method post_interf = this#post
  end	

class in_equality (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post = C.in_equality x y
    method is_interf = false
	method is_interfed = false
	method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
 method post_interf = this#post
  end

class init_thread (fromPC:int) (toPC:int) (vars:Label.t array) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.init_thread vars (C.clone p)
    method is_interf = false
	method is_interfed = false
	method strengthen =C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
 method post_interf = this#post
  end

class kill_thread (fromPC:int) (toPC:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = "Killing thread"
    method post (p:C.t) = C.kill_thread (C.clone p)
    method is_interf = false
		method is_interfed = false
				method strengthen =C.nothing
      method filter (p:C.t) = C.nothing (C.clone p)
 method post_interf = this#post
  end

class lock_acquire_success (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.lock_acquire_success x d false
    method strengthen = C.strengthen_lock_acquire x d
		method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
		method is_interfed = true
    method post_interf = C.lock_acquire_success x d true
  end

class lock_acquire_fail (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.lock_acquire_fail x d
    method strengthen = C.nothing
	method filter = C.nothing 
    method is_interf = false
	method is_interfed = false
    method post_interf = this#post
  end

class lock_release_success (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.lock_release_success x d false
		method strengthen = C.strengthen_lock_release x d
		 method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
		method is_interfed = false
    method post_interf = C.lock_release_success x d true
  end

class lock_release_fail (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.lock_release_fail x d
		method filter (p:C.t) = C.nothing (C.clone p)
		method strengthen = C.nothing
    method is_interf = false
		method is_interfed = false
    method post_interf = this#post
  end
	
class dot_next_assign_lock (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.dot_next_assign_lock x y
		method strengthen = C.strengthen_dot_next_assign_lock x y 
		 method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
		method is_interfed = false
    method post_interf = this#post
  end
	
	
class dot_next_assign_lock_fail (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.dot_next_assign_lock_fail x y
		method strengthen = C.nothing
		 method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = false
		method is_interfed = false
    method post_interf = this#post
  end	


class attempt_mark (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.attempt_mark x y d
		method strengthen = C.strengthen_mark x y d
    method is_interf = true
		method is_interfed = true
    method post_interf = this#post
    method filter = C.nothing
  end
class attempt_mark_fail (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (d:int)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.attempt_mark_fail x y d
    method is_interf = false
		method is_interfed = false
		method strengthen (p:C.t) =C.nothing (C.clone p)
    method filter = C.nothing 
 method post_interf = this#post
  end

class dcas_success_set (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) (t:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.dcas_success_set x y z t
    method strengthen = C.strengthen_dcas_success_set x y z t
    method filter = C.nothing
    method is_interf = true
		method is_interfed = false
    method post_interf = this#post
  end

class cas_success_set (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (d:int) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_success_set x y d z
    method strengthen = C.strengthen_cas_success_set x y d z
    method filter = C.nothing
    method is_interf = true
		method is_interfed = true
    method post_interf = this#post
  end
class dot_next_unmarked_equality (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.dot_next_unmarked_equality x y
    method strengthen = C.strengthen_dot_next_unmarked_equality x y
      method filter (p:C.t) = C.strengthen_dot_next_unmarked_equality x y (C.clone p)
    method is_interf = false
		method is_interfed = true
    method post_interf = this#post
  end
class in_dot_next_unmarked_equality (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.in_dot_next_unmarked_equality x y
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = false
		method is_interfed = true
    method post_interf = this#post
  end
class cas_success (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_success x y z
    method strengthen = C.strengthen_cas_success x y z
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
		method is_interfed = true
    method post_interf = this#post
  end	
class cas_data_success (fromPC:int) (toPC:int) (x:Label.t) (d1:int) (d2:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_data_success x d1 d2
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
    method is_interfed = true
    method post_interf = this#post
  end

class insert_elim (fromPC:int) (toPC:int) (x:Label.t) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.insert_elim x z
    method strengthen = C.nothing
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
    method is_interfed = true
    method post_interf = this#post
  end


class cas_fail (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_fail x y z
    method strengthen = C.nothing
    method filter = C.nothing 
    method is_interf = false
		method is_interfed = false
    method post_interf = this#post
  end	


class cas_next_success (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_next_success x y z
    method strengthen = C.strengthen_cas_next_success x y z
      method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
		method is_interfed = true
    method post_interf = this#post
  end	

class cas_next_fail (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_next_fail x y z
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter = C.nothing 
    method is_interf = false
		method is_interfed = false
    method post_interf = this#post
  end	

class validate_ex_push_pop (fromPC:int) (toPC:int) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) = C.validate_ex_push_pop x (C.clone p)
    method is_interf = true
		method is_interfed = true
	  method strengthen =C.nothing
   method post_interf = C.validate_ex_push_pop x
		method filter (p:C.t) = C.nothing (C.clone p)
  end	

class cas_success_set_mark (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (d:int) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_success_set_mark x y d z
    method strengthen = C.strengthen_cas_success_set_mark x y d z
    method filter (p:C.t) = C.nothing (C.clone p)
    method is_interf = true
		method is_interfed = true
    method post_interf = this#post
  end
	
	
class cas_fail_set (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (d:int) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.cas_fail_set x y d z
    method is_interf = false
	method is_interfed = true
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter  = C.nothing
    method post_interf = this#post
  end		

class dcas_fail_set (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post  = C.dcas_fail_set x y z
    method is_interf = false
		method is_interfed = false
    method strengthen (p:C.t) = C.nothing (C.clone p)
    method filter  = C.filter_dcas_set x y z
    method post_interf = this#post
  end		

let rec fold f acc = function
  | [] -> acc
  | [el] -> (f el) @ acc
  | el::tail -> fold f ((f (C.clone el)) @ acc) tail

class atomic (fromPC:int) (toPC:int) (transformers:transformer list) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) thi = begin
      match transformers with
      | [] -> []
      | head::tail -> 
        let ret = List.fold_left (fun acc (r:transformer) -> fold (fun el -> r#post el thi) [] acc) (head#post (C.clone p) thi) tail in
        ret  
    end
    method strengthen (p:C.t) thi = begin
      match transformers with
      | [] -> []
      | head::tail -> (* a little too much cloning when the previous post returns only one constraint, but fine, let it be *)
	  List.fold_left (fun acc (r:transformer) -> fold (fun el -> r#strengthen el thi) [] acc) (head#strengthen (C.clone p) thi) []
		end
	 method filter (p:C.t) thi = begin
      match transformers with
      | [] -> []
      | head::tail -> (* a little too much cloning when the previous post returns only one constraint, but fine, let it be *)
	  List.fold_left (fun acc (r:transformer) -> fold (fun el -> r#filter el thi) [] acc) (head#filter (C.clone p) thi) []
		end	
    method is_interf = List.exists is_interf transformers
		method is_interfed = List.exists is_interfed transformers
    method post_interf (p:C.t) thi = begin
      match transformers with
      | [] -> []
      | head::tail -> 
        let ret = List.fold_left (fun acc (r:transformer) -> fold (fun el -> r#post_interf el thi) [] acc) (head#post_interf (C.clone p) thi) tail in
        ret  
    end
  end

class cond (fromPC:int) (toPC:int) (transformers:transformer list) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = ""
    method post (p:C.t) thi = begin 
			let rec cond_post oplist p1 thi = 
			begin
      match oplist with
      | [] -> [p1]
      | head::tail ->  let p' = head#post (C.clone p1) thi in if (List.length p') > 0 then begin  (cond_post tail  (List.nth p' 0) thi) end else [p1]
    end in
   cond_post transformers p thi
	end
		method strengthen = C.nothing
      method filter = C.nothing
    method is_interf = false
		method is_interfed = false
    method post_interf = this#post
  end
