module C = Constraint
module R = Rule

module MS_CommitPoint_Empty : Example.E = struct

  let name = "Michael-Scott - wrong commit point for dequeue(empty)"

  let qHead = Label.global (3,"H")
  let qTail = Label.global (4,"T")
  let null = Label.nil
  let bottom = Label.bottom
  let node = Label.local (0,"n")
  let tail = Label.local (1,"t")
  let next = Label.local (2,"next")
  let v = Label.local (0,"v") (* First Argument *)
  let next' = Label.local (0,"next'")
  let head' = Label.local (1,"h'")
  let tail' = Label.local (2,"t'")

  let initial_predicates ob = 
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_queue qHead qTail interesting_colors 0 0
    
  let predicate_transformers ob =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node;tail;next|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 3 node);
(*     (new R.data_assign_var 2 3 node v); *)
    (new R.dot_next_assign 3 4 node null);
    (new R.assign 4 5 tail qTail);
    (new R.assign_dot_next 5 6 next tail);
    (new R.equality 6 7 tail qTail);
    (new R.equality 7 8 next null);  
    (new R.atomic 8 10 [(new R.cas_next_success 8 (-810) tail next node);(new R.validate_insert (-810) 10 "insert" ob node);]);
    (new R.atomic 6 4 [(new R.inequality 6 (-3) tail qTail);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    (new R.atomic 8 4 [(new R.cas_next_fail 8 (-3) tail next node);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    
    (new R.inequality 7 9 next null);
    (new R.atomic 9 4 [(new R.cas_success 9 (-3) qTail tail next);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    (new R.atomic 9 4 [(new R.cas_fail 9 (-3) qTail tail next);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    (new R.atomic 10 11 [(new R.cas_success 10 (-2) qTail tail node);
			  (new R.assign (-2) (-3) node bottom);(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 11 next bottom);]);
    (new R.atomic 10 11 [(new R.cas_fail 10 (-2) qTail tail node);
			  (new R.assign (-2) (-3) node bottom);(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 11 next bottom);]);

    (* loop *)
    (new R.kill_thread 11 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next';head';tail'|]);
    (new R.assign 101 102 head' qHead);
    (new R.assign 102 103 tail' qTail);
    (new R.assign_dot_next 103 104 next' head');
    (new R.equality 104 105 head' qHead);
    (new R.atomic 104 101 [(new R.inequality 104 (-2) head' qHead);
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_promise (-5) 101);]);
    (new R.equality 105 106 head' tail');
    (new R.atomic 106 111 [(new R.equality 106 (-1) next' null);(new R.record_empty (-1) (-3));(new R.validate_empty (-3) (-2) "validateEmpty" ob);
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_return (-5) (-6));(new R.reset_promise (-6) 111);]);
    (new R.inequality 106 108 next' null);
    (new R.atomic 108 101 [(new R.cas_success 108 (-2) qTail tail' next');
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_promise (-5) 101);]);
    (new R.atomic 108 101 [(new R.cas_fail 108 (-2) qTail tail' next');
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_promise (-5) 101);]);

    (new R.atomic 105 109 [(new R.inequality 105 (-1) head' tail');
			    (new R.assign (-1) 109 tail' bottom);]);
    (new R.assign_return 109 110 next');
    (new R.atomic 110 111 [(new R.cas_success 110 (-1) qHead head' next');(new R.validate_delete (-1) (-2) "delete" ob);
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_return (-5) (-6));(new R.reset_promise (-6) 111);]);
    (new R.atomic 110 101 [(new R.cas_fail 110 (-2) qHead head' next');
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_return (-5) (-6));(new R.reset_promise (-6) 101);]);

    (* loop *)
    (new R.kill_thread 111 0);
  ]

end

module MS_NoGC : Example.E = struct

  let name = "Michael-Scott, no GC - no counters"

  let qHead = Label.global (3,"H")
  let qTail = Label.global (4,"T")
  let null = Label.nil
  let bottom = Label.bottom
  let node = Label.local (0,"n")
  let tail = Label.local (1,"t")
  let next = Label.local (2,"next")
  let v = Label.local (0,"v") (* First Argument *)
  let next' = Label.local (0,"next'")
  let head' = Label.local (1,"h'")
  let tail' = Label.local (2,"t'")

  let initial_predicates ob = 
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_queue qHead qTail interesting_colors 0 0
    
  let predicate_transformers ob =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node;tail;next|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 3 node);
(*     (new R.data_assign_var 2 3 node v); *)
    (new R.dot_next_assign 3 4 node null);
    (new R.assign 4 5 tail qTail);
    (new R.assign_dot_next 5 6 next tail);
    (new R.equality 6 7 tail qTail);
    (new R.equality 7 8 next null);  
    (new R.atomic 8 10 [(new R.cas_next_success 8 (-810) tail next node);(new R.validate_insert (-810) 10 "insert" ob node);]);
    (new R.atomic 6 4 [(new R.inequality 6 (-3) tail qTail);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    (new R.atomic 8 4 [(new R.cas_next_fail 8 (-3) tail next node);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    
    (new R.inequality 7 9 next null);
    (new R.atomic 9 4 [(new R.cas_success 9 (-3) qTail tail next);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    (new R.atomic 9 4 [(new R.cas_fail 9 (-3) qTail tail next);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    (new R.atomic 10 11 [(new R.cas_success 10 (-2) qTail tail node);
			  (new R.assign (-2) (-3) node bottom);(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 11 next bottom);]);
    (new R.atomic 10 11 [(new R.cas_fail 10 (-2) qTail tail node);
			  (new R.assign (-2) (-3) node bottom);(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 11 next bottom);]);

    (* loop *)
    (new R.kill_thread 11 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next';head';tail'|]);
    (new R.assign 101 102 head' qHead);
    (new R.assign 102 103 tail' qTail);
    (new R.atomic 103 104 [(new R.assign_dot_next 103 (-1) next' head');(new R.record_empty (-1) 104);]);
    (new R.equality 104 105 head' qHead);
    (new R.atomic 104 101 [(new R.inequality 104 (-2) head' qHead);
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_promise (-5) 101);]);
    (new R.equality 105 106 head' tail');
    (new R.atomic 106 112 [(new R.equality 106 (-1) next' null);(new R.validate_empty (-1) (-2) "validateEmpty" ob);
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_return (-5) (-6));(new R.reset_promise (-6) 112);]);
    (new R.inequality 106 108 next' null);
    (new R.atomic 108 101 [(new R.cas_success 108 (-2) qTail tail' next');
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_promise (-5) 101);]);
    (new R.atomic 108 101 [(new R.cas_fail 108 (-2) qTail tail' next');
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_promise (-5) 101);]);

    (new R.atomic 105 109 [(new R.inequality 105 (-1) head' tail');
			    (new R.assign (-1) 109 tail' bottom);]);
    (new R.assign_return 109 110 next');
    (new R.atomic 110 111 [(new R.cas_success 110 (-1) qHead head' next');(new R.validate_delete (-1) (-2) "delete" ob);
			    (new R.assign (-2) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_return (-5) (-6));(new R.reset_promise (-6) 111);]);
    (new R.atomic 110 101 [(new R.cas_fail 110 (-2) qHead head' next');
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_return (-5) (-6));(new R.reset_promise (-6) 101);]);

    (new R.free_cell 111 112 head');
    (new R.kill_thread 112 0);
  ]

end

module MS_Swap : Example.E = struct

  let name = "Michael-Scott - swapping instructions"

  let qHead = Label.global (3,"H")
  let qTail = Label.global (4,"T")
  let null = Label.nil
  let bottom = Label.bottom
  let node = Label.local (0,"n")
  let tail = Label.local (1,"t")
  let next = Label.local (2,"next")
  let v = Label.local (0,"v") (* First Argument *)
  let next' = Label.local (0,"next'")
  let head' = Label.local (1,"h'")
  let tail' = Label.local (2,"t'")

  let initial_predicates ob = 
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_queue qHead qTail interesting_colors 0 0
    
  let predicate_transformers ob =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node;tail;next|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 3 node);
(*     (new R.data_assign_var 2 3 node v); *)
    (new R.dot_next_assign 3 4 node null);
    (new R.assign 4 5 tail qTail);
    (new R.assign_dot_next 5 6 next tail);
    (new R.equality 6 7 tail qTail);
    (new R.equality 7 8 next null);  
    (new R.atomic 8 10 [(new R.cas_next_success 8 (-810) tail next node);(new R.validate_insert (-810) 10 "insert" ob node);]);
    (new R.atomic 6 4 [(new R.inequality 6 (-3) tail qTail);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    (new R.atomic 8 4 [(new R.cas_next_fail 8 (-3) tail next node);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    
    (new R.inequality 7 9 next null);
    (new R.atomic 9 4 [(new R.cas_success 9 (-3) qTail tail next);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    (new R.atomic 9 4 [(new R.cas_fail 9 (-3) qTail tail next);
			(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 4 next bottom);]);
    (new R.atomic 10 11 [(new R.cas_success 10 (-2) qTail tail node);
			  (new R.assign (-2) (-3) node bottom);(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 11 next bottom);]);
    (new R.atomic 10 11 [(new R.cas_fail 10 (-2) qTail tail node);
			  (new R.assign (-2) (-3) node bottom);(new R.assign (-3) (-4) tail bottom);(new R.assign (-4) 11 next bottom);]);

    (* loop *)
    (new R.kill_thread 11 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next';head';tail'|]);
    (new R.assign 101 102 head' qHead);
    (new R.atomic 102 103 [(new R.assign_dot_next 102 (-1) next' head');(new R.record_empty (-1) 103);]);
    (new R.assign 103 104 tail' qTail);
    (new R.equality 104 105 head' qHead);
    (new R.atomic 104 101 [(new R.inequality 104 (-2) head' qHead);
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_promise (-5) 101);]);
    (new R.equality 105 106 head' tail');
    (new R.atomic 106 111 [(new R.equality 106 (-1) next' null);(new R.validate_empty (-1) (-2) "validateEmpty" ob);
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_return (-5) (-6));(new R.reset_promise (-6) 111);]);
    (new R.inequality 106 108 next' null);
    (new R.atomic 108 101 [(new R.cas_success 108 (-2) qTail tail' next');
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_promise (-5) 101);]);
    (new R.atomic 108 101 [(new R.cas_fail 108 (-2) qTail tail' next');
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_promise (-5) 101);]);

    (new R.atomic 105 109 [(new R.inequality 105 (-1) head' tail');
			    (new R.assign (-1) 109 tail' bottom);]);
    (new R.assign_return 109 110 next');
    (new R.atomic 110 111 [(new R.cas_success 110 (-1) qHead head' next');(new R.validate_delete (-1) (-2) "delete" ob);
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_return (-5) (-6));(new R.reset_promise (-6) 111);]);
    (new R.atomic 110 101 [(new R.cas_fail 110 (-2) qHead head' next');
			    (new R.assign (-2) (-3) head' bottom);(new R.assign (-3) (-4) tail' bottom);(new R.assign (-4) (-5) next' bottom);
			    (new R.reset_return (-5) (-6));(new R.reset_promise (-6) 101);]);

    (* loop *)
    (new R.kill_thread 111 0);
  ]

end


module TwoLocksQueue_CommitPointsUnlock : Example.E = struct

  let name = "Two-locks queue - wrong commit point for insertion"

  let qHead = Label.global (3,"H")
  let qTail = Label.global (4,"T")
  let null = Label.nil
  let node = Label.local (0,"n")
  let next' = Label.local (0,"next'")
  let head' = Label.local (1,"h'")

  let lockH = 0
  let lockT = 1

  let initial_predicates ob = 
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_queue qHead qTail interesting_colors 0 2

  let predicate_transformers ob =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 2 node);
(*     (new R.data_assign_var 3 4 node v); *)
    (new R.dot_next_assign 2 4 node null);
    (new R.main_lock 4 5 lockT);
    (new R.dot_next_assign 5 6 qTail node);
    (new R.assign 6 7 qTail node);
    (new R.atomic 7 8 [(new R.main_unlock 7 (-1) lockT);(new R.validate_insert (-1) 8 "insert" ob node);]);

    (new R.kill_thread 8 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next';head'|]);
    (new R.main_lock 101 102 lockH);

    (new R.assign 102 103 head' qHead);
    (new R.atomic 103 104 [(new R.assign_dot_next 103 (-1) next' head');(new R.record_empty (-1) 104);]);

    (new R.equality 104 105 next' null);
    (new R.atomic 105 110 [(new R.main_unlock 105 (-1) lockH);(new R.validate_empty (-1) 110 "validateEmpty" ob);]);

    (new R.inequality 104 107 next' null);
    (new R.assign_return 107 108 next');
    (new R.assign 108 109 qHead next');
    (new R.atomic 109 110 [(new R.main_unlock 109 (-1) lockH);(new R.validate_delete (-1) 110 "delete" ob);]);

    (new R.kill_thread 110 0);
  ]

end

module Treiber_noGC : Example.E = struct

  let name = "Treiber no GC - no counters"

  let s = Label.global (3,"S")
  let null = Label.nil
  let bottom = Label.bottom
  let x = Label.local (0,"x")
  let t = Label.local (1,"t")
  let t' = Label.local (0,"t'")
  let x' = Label.local (1,"x'")

  let initial_predicates ob =
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_stack s interesting_colors 0 0

  let predicate_transformers ob =
    [
    (* ============================ push =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|x;t|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 4 x);
(*     (new R.data_assign_var 3 4 x v); *)
    (new R.assign 4 5 t s);
    (new R.dot_next_assign 5 6 x t);
    (new R.atomic 6 4 [(new R.cas_fail 6 (-64) s t x);
			(new R.assign (-64) 4 t bottom);]);
    (new R.atomic 6 7 [(new R.cas_success 6 (-67) s t x);(new R.validate_insert (-67) (-77) "insert" ob x);
			(new R.assign (-77) (-777) t bottom);(new R.assign (-777) 7 x bottom);]);

    (new R.kill_thread 7 0);
    
    (* ============================ pop =============================== *)
    (new R.init_thread 0 12 [|t';x'|]);
    (new R.atomic 12 13 [(new R.assign 12 (-1) t' s);(new R.record_empty (-1) 13);]);
    (new R.atomic 13 19 [(new R.equality 13 (-1) t' null);(new R.validate_empty (-1) (-2) "validateEmpty" ob);
			  (new R.assign (-2) (-3) t' bottom);(new R.assign (-3) (-4) x' bottom);
			  (new R.reset_return (-4) (-5));(new R.reset_promise (-5) 19);]);

    (new R.inequality 13 15 t' null);
    (new R.assign_dot_next 15 16 x' t');
    (new R.assign_return 16 17 t');
    (new R.atomic 17 12 [(new R.cas_fail 17 (-1) s t' x');
			  (new R.assign (-1) (-2) t' bottom);(new R.assign (-2) (-3) x' bottom);
			  (new R.reset_return (-3) (-4));(new R.reset_promise (-4) 12);]);
    (new R.atomic 17 18 [(new R.cas_success 17 (-1) s t' x');(new R.validate_delete (-1) (-2) "delete" ob);
			  (new R.assign (-3) (-4) x' bottom);
			  (new R.reset_return (-4) (-5));(new R.reset_promise (-5) 18);]);
    
    (new R.free_cell 18 19 t');
    (new R.kill_thread 19 0);
  ]

end

module Treiber_OmittingData : Example.E = struct

  let name = "Treiber omitting data"

  let s = Label.global (3,"S")
  let null = Label.nil
  let bottom = Label.bottom
  let x = Label.local (0,"x")
  let t = Label.local (1,"t")
  let t' = Label.local (0,"t'")
  let x' = Label.local (1,"x'")

  let initial_predicates ob =
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_stack s interesting_colors 0 0

  let predicate_transformers ob =
    [
    (* ============================ push =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|x;t|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 4 x);
(*     (new R.data_assign_var 3 4 x v); *)
    (new R.assign 4 5 t s);
    (new R.dot_next_assign 5 6 x t);
    (new R.atomic 6 4 [(new R.cas_fail 6 (-64) s t x);
			(new R.assign (-64) 4 t bottom);]);
    (new R.atomic 6 7 [(new R.cas_success 6 (-67) s t x);(new R.validate_insert' (-67) (-77) "insert" ob x);
			(new R.assign (-77) (-777) t bottom);(new R.assign (-777) 7 x bottom);]);

    (new R.kill_thread 7 0);
    
    (* ============================ pop =============================== *)
    (new R.init_thread 0 12 [|t';x'|]);
    (new R.atomic 12 13 [(new R.assign 12 (-1) t' s);(new R.record_empty (-1) 13);]);
    (new R.atomic 13 18 [(new R.equality 13 (-1) t' null);(new R.validate_empty (-1) (-2) "validateEmpty" ob);
			  (new R.assign (-2) (-3) t' bottom);(new R.assign (-3) (-4) x' bottom);
			  (new R.reset_return (-4) (-5));(new R.reset_promise (-5) 18);]);

    (new R.inequality 13 15 t' null);
    (new R.assign_dot_next 15 16 x' t');
    (new R.assign_return 16 17 t');
    (new R.atomic 17 12 [(new R.cas_fail 17 (-1) s t' x');
			  (new R.assign (-1) (-2) t' bottom);(new R.assign (-2) (-3) x' bottom);
			  (new R.reset_return (-3) (-4));(new R.reset_promise (-4) 12);]);
    (new R.atomic 17 18 [(new R.cas_success 17 (-1) s t' x');(new R.validate_delete (-1) (-2) "delete" ob);
			  (new R.assign (-2) (-3) t' bottom);(new R.assign (-3) (-4) x' bottom);
			  (new R.reset_return (-4) (-5));(new R.reset_promise (-5) 18);]);
    
    (new R.kill_thread 18 0);
  ]

end
