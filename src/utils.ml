
module S = Set.Make(struct type t = int let compare = Pervasives.compare end)
exception FailTest

class all_injections n m check_answer =
object(this)

  val mutable table = Array.make_matrix n m 0
  val mutable answer = Array.make n None
  val mutable finito = false
  method hasMore: bool = not(finito)
  method next: unit = begin
    let rec addOne i j = begin
      if i < 0 then finito <- true
      else begin 
	if j < 0 then addOne (i - 1) (pred m) else begin
	  if table.(i).(j) = 0
	  then begin
	    table.(i).(j) <- 1;
	    try check_answer table n m answer; with FailTest -> addOne (pred n) (pred m);
	  end else begin
	    table.(i).(j) <- 0;
	    addOne i (j-1)
	  end
	end;
      end
    end in
    addOne (pred n) (pred m)
  end      

  (* will position the answer at the right place *)
  method init = try check_answer table n m answer; with FailTest -> this#next

(*   method reset: unit = begin *)
(*     for i = 0 to pred n do for j = 0 to pred m do table.(i).(j) <- 0; done; done; *)
(*     finito <- false; *)
(*     this#init *)
(*   end *)

  method print = begin
    Debug.print "Injection:\n";
    for i = 0 to pred n do for j = 0 to pred m do Debug.print "%d " table.(i).(j); done; Debug.print "\n"; done;
    Debug.print "Answer:\n";
    let string_of_answer = function None -> "x" | Some k -> string_of_int k in
    for i = 0 to pred n do Debug.print "%d -> %s, " i (string_of_answer answer.(i)); done;
  end

end (* // class all_injections *)

(* ========================================================================================================= *)
(* =====================                      Powerset and injections               ======================== *)
(* ========================================================================================================= *)

let check_injection t n m a = begin
  for k = 0 to pred n do a.(k) <- None done;
  let s = ref S.empty in
  (* pass the check of lines *)
  for i = 0 to pred n do
    let found = ref false in
    for j = 0 to pred m do
      if t.(i).(j) = 1 then begin
	if !found then raise FailTest; (* illegal mapping if I have 2 ones on the same line *)
	found := true;
	a.(i) <- Some(j);
	(* pass the check of columns *)
	if S.mem j !s then raise FailTest; (* illegal mapping if I have 2 ones on the same column *)
	s := S.add j !s;
      end;
    done;
  done;
end

class powerinjections n m =
object(this)
  inherit all_injections n m check_injection
  method get: ( (int option) * (int option) ) list = begin
    let res = ref [] in
    Array.iteri (fun a b -> res := (Some a,b) :: !res) answer;
    let tmp = Array.make m 0 in
    Array.iter (fun b -> match b with None -> () | Some j -> tmp.(j) <- 1) answer;
    Array.iteri (fun j test -> if test = 0 then res := (None,Some j) :: !res) tmp;
    !res
  end
    
end (* // class powerinjections *)

class injections n m =
object(this)
  inherit all_injections n m (fun t' n' m' a' -> check_injection t' n' m' a'; Array.iter (function None -> raise FailTest | _ -> ()) a')
  method get: int array = Array.map (function None -> failwith("should not happen") | Some v -> v) answer
end (* // class injections *)

(* ========================================================================================================= *)
(* =====================                      Ordered  Cyclic_Injections            ======================== *)
(* ========================================================================================================= *)

let check_cyclic_injection t n m a = begin
  for k = 0 to pred n do a.(k) <- None done;
  let s = ref S.empty in
  let inf, sup = ref (-1), ref (-1) in
  (* pass the check of lines *)
  for i = 0 to pred n do
    let found = ref false in
    for j = 0 to pred m do
      if t.(i).(j) = 1 then begin
	if !found then raise FailTest; (* illegal mapping if I have 2 ones on the same line *)
	found := true;
	a.(i) <- Some(j);
	(* pass the check of columns *)
	if S.is_empty !s then begin 
	  inf := j; sup := j;
	end else begin
	  let c = if j < !inf then j+m else j in
	  if c < !sup then raise FailTest; (* Not keeping a cyclic order *)
	  sup := c;
	  if S.mem j !s then raise FailTest; (* illegal mapping if I have 2 ones on the same column *)
	end;
	s := S.add j !s;
      end;
    done;
  done;
  Array.iter (function None -> raise FailTest | _ -> ()) a
end

class ordered_cyclic_injections n m =
object(this)
  inherit all_injections n m check_cyclic_injection
  method get: int array = Array.map (function None -> failwith("should not happen") | Some v -> v) answer
end (* // class ordered_cyclic_injections *)


(* ========================================================================================================= *)
(* =====================                      Cache                                 ======================== *)
(* ========================================================================================================= *)

type mapping = (int option) * (int option)
exception NotCached
class ['a] cache n m =
  object(this) 
      
    val c = Array.make_matrix n m None
    val cn2 = Array.make m None
    val c2n = Array.make n None
	
    method get mapping : 'a = begin
      match mapping with
      | None,None -> failwith("eh?")
      | None, Some b -> (match cn2.(b) with None -> raise NotCached | Some d -> d )
      | Some a, None -> (match c2n.(a) with None -> raise NotCached | Some d -> d )
      | Some a, Some b -> (match c.(a).(b) with None -> raise NotCached | Some d -> d )
    end
    method set mapping (d:'a) : unit = begin
      match mapping with
      | None,None -> failwith("eh?")
      | None, Some b -> cn2.(b) <- Some d
      | Some a, None -> c2n.(a) <- Some d
      | Some a, Some b -> c.(a).(b) <- Some d
    end

    method print (f: 'a -> unit) : unit = begin
      Debug.print "Cache (%d x %d)" n m;
      Array.iter (fun a -> Printf.printf "\n"; Debug.print ""; Array.iter (fun b -> match b with None -> Printf.printf "%-7s " "?"; | Some d -> f d) a;) c;
      Debug.print "\n";
      Debug.print "Cache Null to %d" m;
      Array.iter (fun b -> Printf.printf "\n"; Debug.print ""; match b with None -> Printf.printf "%-7s " "?"; | Some d -> f d) cn2;
      Debug.print "\n";
      Debug.print "Cache %d to Null" m;
      Array.iter (fun a -> Printf.printf "\n"; Debug.print ""; match a with None -> Printf.printf "%-7s " "?"; | Some d -> f d) c2n;
      Debug.print "\n";
    end
  end


(* ============================================================================================ *)
(* =====================                      Powerset                 ======================== *)
(* ============================================================================================ *)

class ['a] powerset (elts:'a list) =
  let n = List.length elts in
  let pred_n = pred n in
  let (elements:'a array) = Array.of_list elts in
object(this)

  val mutable bin = Array.make n 0
  val mutable finito = false
  method hasMore: bool = not(finito)
  method next: unit = begin
    let rec addOne i =
      if i < 0 then finito <- true
      else ( if bin.(i) = 0 then bin.(i) <- 1 else ( bin.(i) <- 0; addOne (i-1) ); );
    in addOne pred_n
  end      

  method get = begin
    let res = ref [] in
    Array.iteri (fun i j -> if j = 1 then res := elements.(i) :: !res; ) bin;
    !res
  end

end (* // class powerset *)


(* ============================================================================================ *)
(* =====================                      Powerset                 ======================== *)
(* ============================================================================================ *)
class permutations n =
object(this)
  val mutable table = Array.make_matrix n n 0
  val mutable answer = Array.make n (-1)
  val mutable finito = false
  method hasMore: bool = not(finito)

  method private check: unit = begin
    for k = 0 to pred n do answer.(k) <- (-1) done; (* reset *)
    let s = ref S.empty in
    (* pass the check of lines *)
    for i = 0 to pred n do
      let found = ref false in
      for j = 0 to pred n do
	if table.(i).(j) = 1 then begin
	  if !found then raise FailTest; (* illegal mapping if I have 2 ones on the same line *)
	  found := true;
	  answer.(i) <- j;
	  (* pass the check of columns *)
	  if S.mem j !s then raise FailTest; (* illegal mapping if I have 2 ones on the same column *)
	  s := S.add j !s;
	end;
      done;
      if not(!found) then raise FailTest; (* illegal mapping: I must map it somewhere *)
    done;
  end

  method next: unit = begin
    let rec addOne i j = begin
      if i < 0 then finito <- true
      else begin 
	if j < 0 then addOne (i - 1) (pred n) else begin
	  if table.(i).(j) = 0
	  then begin
	    table.(i).(j) <- 1;
	    try this#check; (* this#print; Debug.print "I pass the check\n"; *)
	    with FailTest -> addOne (pred n) (pred n);
	  end else begin
	    table.(i).(j) <- 0;
	    addOne i (j-1)
	  end
	end;
      end
    end in
    addOne (pred n) (pred n)
  end      

  (* will position the answer at the right place *)
  method init = this#next

  method print = begin
    Debug.print "Injection:\n";
    for i = 0 to pred n do for j = 0 to pred n do Debug.print "%d " table.(i).(j); done; Debug.print "\n"; done;
    Debug.print "Answer:\n";
    for i = 0 to pred n do Debug.print "%d -> %d, " i answer.(i); done;
  end

  method get: int array = answer
    
end (* // class permutations *)

let permute list = begin
  let all = Array.of_list list in
  let n = Array.length all in
  assert( n>0 );
  let mappings = new permutations n in
  mappings#init;
  let res = ref [] in
  while mappings#hasMore do
    res := (Array.fold_left (fun acc j -> all.(j) :: acc) [] (mappings#get)) :: !res;
    mappings#next;
  done;
  assert( List.length !res > 0 );
  !res
end
