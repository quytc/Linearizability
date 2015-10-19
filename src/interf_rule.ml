(* ========================================================================================================= *)
(* =====================                  Predicate Transformer                     ======================== *)
(* ========================================================================================================= *)
let sprintf = Printf.sprintf

let debug = false
let pause = false

module C = Constraint
type cons = C.t


  (** The concrete type of a transformer. *)
class type transformer =
  object
    method post: cons -> int -> cons list
    method post_interf: cons -> int -> cons list
    method is_interf: bool
    method toString: string
    method fromPC: int
    method toPC: int
  end

type t = transformer
      
let string_of (r:t) = r#toString

let post r c = begin
				
  let nth = C.nthreads c in
  let rec post_rec thi acc =
  (*  if thi = nth then acc else begin
      post_rec (thi+1) 
	*)			
				
	if (C.pc c thi) = r#fromPC then begin
	try match r#post c thi with
	| [] -> acc
	| all ->
	    let finals = List.fold_left (fun accu p -> begin
	      C.set_pc p thi r#toPC;
	      C.set_in_queue p false;
	      C.set_in_slice p false;
	      if !Globals.trace then begin 
		C.set_parent p c;
		C.log p (lazy (sprintf "%d (Thread %d from %d, at pc %d): %s" (C.id p) thi (C.id c) r#fromPC (string_of r)));
	      end;
	      [p] @ accu
	    end) acc all
	    in
	    finals
	with C.IgnoreConstraint -> print_string "---end3";
	  if debug then Debug.print "%s Ignoring the constraint (%d)%s %s\n" Debug.red (C.id c) (C.string_of c) Debug.noColor;
	  acc
      end else acc
  in  post_rec 0 []
				
end


(*
let post r c = begin
  let nth = C.nthreads c in
  let rec post_rec thi acc =
		if thi = nth then acc else begin
      post_rec (thi+1) (if (C.pc c thi) = r#fromPC then begin
				try match r#post c thi with
	| [] -> acc
	| all -> 
	    let finals = List.fold_left (fun accu p -> begin
	      C.set_pc p thi r#toPC;
	      C.set_in_queue p false;
	      C.set_in_slice p false;
	      [p] @ accu
	    end) acc all
	    in
	     finals
	with C.IgnoreConstraint ->
	  if debug then Debug.print "%s Ignoring the constraint (%d)%s %s\n" Debug.red (C.id c) (C.string_of c) Debug.noColor;
	  acc
      end else acc)
    end
  in 
	post_rec 0 []
end
*)
let post_interf r c  = begin
			
   let nth = C.nthreads c in
   let rec post_rec thi acc =	
	 if (C.pc c thi) = r#fromPC then begin
	 try match r#post_interf c thi with
	  | [] -> acc
	  | all -> 
	    let finals = List.fold_left (fun accu p -> begin
	     [p] @ accu
	    end) acc all
	    in
	    finals
	with C.IgnoreConstraint ->
	  if debug then Debug.print "%s Ignoring the constraint (%d)%s %s\n" Debug.red (C.id c) (C.string_of c) Debug.noColor;
	  acc
      end else acc
  in  post_rec 0 []
end

let is_interf r = r#is_interf


(* ============================ Transformer implementation ======================================== *)



class assign (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s := %s" (Label.string_of x) (Label.string_of y)
    method post (p:C.t) = C.assign x y (C.clone p)
    method is_interf = not(Label.is_local x)
    method post_interf p thi = if Label.is_local x then [] else this#post p thi
  end

class dot_next_assign (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.next := %s" (Label.string_of x) (Label.string_of y)
    method post (p:C.t) = C.dot_next_assign x y (C.clone p)
    method is_interf = false
    method post_interf = this#post
  end
class dot_next_assign_dot_next (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.next := %s" (Label.string_of x) (Label.string_of y)
    method post (p:C.t) = C.dot_next_assign_dot_next x y (C.clone p)
    method is_interf = false
    method post_interf = this#post
  end
class data_assign (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.data := %s" (Label.string_of x) "d"
    method post (p:C.t) = C.data_assign x d (C.clone p)
    method is_interf = false
    method post_interf = this#post
  end
	
class data_equality (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.data := %s" (Label.string_of x) "d"
    method post (p:C.t) = C.data_equality x d (C.clone p)
    method is_interf = false
    method post_interf = this#post
  end
	
	class get_marked_assign_dot_next (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (marked:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.next == %s" (Label.string_of x) ""
    method post = C.get_marked_assign_dot_next x y marked 
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end
	
	
class data_inequality (fromPC:int) (toPC:int) (x:Label.t) (d:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.data := %s" (Label.string_of x) "d"
    method post (p:C.t) = C.data_inequality x d (C.clone p)
    method is_interf = false
    method post_interf = this#post
  end
class data_equality_variable (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.data := %s" (Label.string_of x) "d"
    method post (p:C.t) = C.data_equality_variable x y (C.clone p)
    method is_interf = false
    method post_interf = this#post
  end
class assign_dot_next (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s := %s.next" (Label.string_of x) (Label.string_of y)
    method post (p:C.t) = C.assign_dot_next x y (C.clone p)
    method is_interf = true
    method post_interf p thi = if Label.is_local x then [] else this#post p thi
  end

(* local label only *)
class new_cell (fromPC:int) (toPC:int) ?(gc=false) (x:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s := new cell ()" (Label.string_of x)
    method post (p:C.t) thi = C.make_new_cell x (C.clone p) thi
    method is_interf = false
    method post_interf = this#post
  end

class next_equality (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.next == %s" (Label.string_of x) (Label.string_of y)
    method post = C.next_equality x y
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end
	
class equality (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.next == %s" (Label.string_of x) (Label.string_of y)
    method post = C.equality x y
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end

class less_than (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.next == %s" (Label.string_of x) (Label.string_of y)
    method post = C.less_than x y
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end	

class in_equality (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.next == %s" (Label.string_of x) (Label.string_of y)
    method post = C.in_equality x y
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end

class nextReference (fromPC:int) (toPC:int) (x:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.next == %s" (Label.string_of x) ""
    method post = C.nextReference x 
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end

class inNextReference(fromPC:int) (toPC:int) (x:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "%s.next == %s" (Label.string_of x) ""
    method post = C.inNextReference x 
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end
	

class init_thread (fromPC:int) (toPC:int) (vars:Label.t array) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = Array.fold_left (fun acc v -> sprintf "%s%s|" acc (Label.string_of v)) "Initializing thread with |" vars
    method post (p:C.t) = C.init_thread vars (C.clone p)
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end

class kill_thread (fromPC:int) (toPC:int) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = "Killing thread"
    method post (p:C.t) = C.kill_thread (C.clone p)
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end

class cas_success (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "CAS_success(%s,%s,%s)" (Label.string_of x) (Label.string_of y) (Label.string_of z)
    method post  = C.cas_success x y z
    method is_interf = true
    method post_interf = C.cas_success x y z
  end

class attempt_mark (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "CAS_success(%s,%s)" (Label.string_of x) "d"
    method post  = C.attempt_mark x y
    method is_interf = true
    method post_interf = C.attempt_mark x y
  end
class attempt_mark_fail (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t)  =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "CAS_success(%s,%s)" (Label.string_of x) "d"
    method post  = C.attempt_mark_fail x y
    method is_interf = true
    method post_interf = C.attempt_mark_fail x y
  end
class cas_success_set (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (d:int) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "CAS_success(%s,%s,%s)" (Label.string_of x) (Label.string_of y) (Label.string_of z)
    method post  = C.cas_success_set x y d z
    method is_interf = true
    method post_interf = C.cas_success_set x y d z
  end

class cas_fail_set (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (d:int) (z:Label.t) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "CAS_success(%s,%s,%s)" (Label.string_of x) (Label.string_of y) (Label.string_of z)
    method post  = C.cas_fail_set x y d z
    method is_interf = true
    method post_interf = C.cas_fail_set x y d z
  end		
	
class cas_fail (fromPC:int) (toPC:int) (x:Label.t) (y:Label.t) (z:Label.t) =
  object(this)
    inherit in_equality fromPC toPC x y
    method toString = sprintf "CAS_fail(%s,%s,%s)" (Label.string_of x) (Label.string_of y) (Label.string_of z)
  end

let rec fold f acc = function
  | [] -> acc
  | [el] -> (f el) @ acc
  | el::tail -> fold f ((f (C.clone el)) @ acc) tail

class atomic (fromPC:int) (toPC:int) (transformers:transformer list) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = begin
      let str = (List.fold_left (fun acc r -> sprintf "%s%s | " acc (string_of r)) "" transformers) in
      sprintf "< %s >" (Str.string_before str ((String.length str) - 1))
    end
    method post (p:C.t) thi = begin
      match transformers with
      | [] -> []
      | head::tail -> (* a little too much cloning when the previous post returns only one constraint, but fine, let it be *)
	  assert( head#fromPC = fromPC && (List.hd (List.rev transformers))#toPC = toPC );
(* 	  List.fold_left (fun acc (r:transformer) -> List.fold_left (fun acc' el -> (r#post (C.clone el) thi) @ acc') [] acc) (head#post (C.clone p) thi) tail *)
	  List.fold_left (fun acc (r:transformer) -> fold (fun el -> r#post el thi) [] acc) (head#post (C.clone p) thi) tail

    end
    method is_interf = List.exists is_interf transformers
    method post_interf = this#post
  end
    

class record_insert (fromPC:int) (toPC:int) (data:Data.t list) =
  object(this)
    method fromPC = fromPC
    method toPC = toPC
    method toString = sprintf "record an insertion of %s" (List.fold_left (fun acc d -> sprintf "%s%c," acc (Data.char_of d)) "" data)
    method post = C.record_insert data (* no need to clone *)
    method is_interf = false
    method post_interf (_:C.t) (_:int) : C.t list = []
  end
