module C = Constraint
module R = Rule

module Stack : Example.E = struct

  let name = "Coarse Stack"

  let s = Label.global (3,"S")
  let null = Label.nil
  let node = Label.local (0,"n")
  let x' = Label.local (0,"x'")
  let v = Label.local (0,"v")

  let lock = 0

  let initial_predicates ob =
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_stack s interesting_colors 0 1

  let predicate_transformers ob =
    [
    (* ============================ push =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.main_lock 1 2 lock);
    (new R.new_cell 2 4 node);
(*     (new R.data_assign_var 3 4 node v); *)
    (new R.dot_next_assign 4 5 node s);
    (new R.atomic 5 6 [(new R.assign 5 (-1) s node);(new R.validate_insert (-1) 6 "insert" ob node); ]);
    (new R.main_unlock 6 7 lock);

    (new R.kill_thread 7 0);

    (* ============================ pop =============================== *)
    (new R.init_thread 0 101 [|x'|]);
    (new R.main_lock 101 102 lock);

    (new R.atomic 102 103 [(new R.equality 102 (-1) s null);(new R.record_empty (-1) 103);]);
    (new R.atomic 103 109 [(new R.main_unlock 103 (-1) lock);(new R.validate_empty (-1) 109 "validateEmpty" ob);]);

    (new R.inequality 102 105 s null);
    (new R.assign_dot_next 105 106 x' s);
    (new R.assign_return 106 107 s);
    (new R.atomic 107 108 [(new R.assign 107 (-1) s x');(new R.validate_delete (-1) 108 "delete" ob)]);
    (new R.main_unlock 108 109 lock);

    (new R.kill_thread 109 0);
  ]

end

module StackNoGC : Example.E = struct

  let name = "Coarse Stack - No GC"

  let s = Label.global (3,"S")
  let null = Label.nil
  let node = Label.local (0,"n")
  let x' = Label.local (0,"x'")
  let t' = Label.local (1,"t'")

  let lock = 0

  let initial_predicates ob =
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_stack s interesting_colors 0 1

  let predicate_transformers ob =
    [
    (* ============================ push =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.main_lock 1 2 lock);
    (new R.new_cell 2 4 node);
(*     (new R.data_assign_var 3 4 node v); *)
    (new R.dot_next_assign 4 5 node s);
    (new R.atomic 5 6 [(new R.assign 5 (-1) s node);(new R.validate_insert (-1) 6 "insert" ob node); ]);
    (new R.main_unlock 6 7 lock);

    (new R.kill_thread 7 0);

    (* ============================ pop =============================== *)
    (new R.init_thread 0 101 [|x';t'|]);
    (new R.main_lock 101 102 lock);

    (new R.assign 102 103 t' s);
    (new R.atomic 103 104 [(new R.equality 103 (-1) t' null);(new R.record_empty (-1) 104);]);
    (new R.atomic 104 111 [(new R.main_unlock 104 (-1) lock);(new R.validate_empty (-1) 111 "validateEmpty" ob);]);

    (new R.inequality 103 105 t' null);
    (new R.assign_dot_next 105 106 x' t');
    (new R.assign_return 106 107 t');
    (new R.atomic 107 108 [(new R.assign 107 (-1) s x');(new R.validate_delete (-1) 108 "delete" ob)]);
    (new R.main_unlock 108 109 lock);

    (new R.free_cell 109 111 t');

    (new R.kill_thread 111 0);
  ]

end

module Queue : Example.E = struct

  let name = "Coarse queue"

  let qHead = Label.global (3,"H")
  let qTail = Label.global (4,"T")
  let null = Label.nil
  let node = Label.local (0,"n")
  let head' = Label.local (0,"h'")
  let next' = Label.local (1,"next'")

  let lock = 0

  let initial_predicates ob = 
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_queue qHead qTail interesting_colors 0 1

  let predicate_transformers ob =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 2 node);
(*     (new R.data_assign_var 3 4 node v); *)
    (new R.dot_next_assign 2 4 node null);
    (new R.main_lock 4 5 lock);
    (new R.atomic 5 6 [(new R.dot_next_assign 5 (-1) qTail node);(new R.validate_insert (-1) 6 "insert" ob node);]);
    (new R.assign 6 7 qTail node);
    (new R.main_unlock 7 8 lock);

    (new R.kill_thread 8 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|head';next'|]);
    (new R.main_lock 101 102 lock);

    (new R.assign 102 103 head' qHead);
    (new R.atomic 103 104 [(new R.assign_dot_next 103 (-1) next' head');(new R.record_empty (-1) 104);]);

    (new R.equality 104 105 next' null);
    (new R.atomic 105 110 [(new R.main_unlock 105 (-1) lock);(new R.validate_empty (-1) 110 "validateEmpty" ob);]);

    (new R.inequality 104 107 next' null);
    (new R.assign_return 107 108 next');
    (new R.atomic 108 109 [(new R.assign 108 (-1) qHead next');(new R.validate_delete (-1) 109 "delete" ob);]);
    (new R.main_unlock 109 110 lock);

    (new R.kill_thread 110 0);
  ]

end

module QueueNoGC : Example.E = struct

  let name = "Coarse queue - No GC"

  let qHead = Label.global (3,"H")
  let qTail = Label.global (4,"T")
  let null = Label.nil
  let node = Label.local (0,"n")
  let next' = Label.local (0,"next'")
  let head' = Label.local (1,"h'")

  let lock = 0

  let initial_predicates ob = 
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_queue qHead qTail interesting_colors 0 1

  let predicate_transformers ob =
    [
    (* ============================ enqueue =============================== *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 2 node);
(*     (new R.data_assign_var 3 4 node v); *)
    (new R.dot_next_assign 2 4 node null);
    (new R.main_lock 4 5 lock);
    (new R.atomic 5 6 [(new R.dot_next_assign 5 (-1) qTail node);(new R.validate_insert (-1) 6 "insert" ob node);]);
    (new R.assign 6 7 qTail node);
    (new R.main_unlock 7 8 lock);

    (new R.kill_thread 8 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next';head'|]);
    (new R.main_lock 101 102 lock);

    (new R.assign 102 103 head' qHead);
    (new R.atomic 103 104 [(new R.assign_dot_next 103 (-1) next' head');(new R.record_empty (-1) 104);]);

    (new R.equality 104 105 next' null);
    (new R.atomic 105 111 [(new R.main_unlock 105 (-1) lock);(new R.validate_empty (-1) 111 "validateEmpty" ob);]);

    (new R.inequality 104 107 next' null);
    (new R.assign_return 107 108 next');
    (new R.atomic 108 109 [(new R.assign 108 (-1) qHead next');(new R.validate_delete (-1) 109 "delete" ob);]);
    (new R.main_unlock 109 110 lock);

    (new R.free_cell 110 111 head');

    (new R.kill_thread 111 0);
  ]

end

module TwoLocksQueue : Example.E = struct

  let name = "Two-locks queue"

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
    (new R.atomic 5 6 [(new R.dot_next_assign 5 (-1) qTail node);(new R.validate_insert (-1) 6 "insert" ob node);]);
    (new R.assign 6 7 qTail node);
    (new R.main_unlock 7 8 lockT);

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
    (new R.atomic 108 109 [(new R.assign 108 (-1) qHead next');(new R.validate_delete (-1) 109 "delete" ob);]);
    (new R.main_unlock 109 110 lockH);

    (new R.kill_thread 110 0);
  ]

end

module TwoLocksQueue_NoGC : Example.E = struct

  let name = "Two-locks queue - No GC"

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
    (new R.atomic 5 6 [(new R.dot_next_assign 5 (-1) qTail node);(new R.validate_insert (-1) 6 "insert" ob node);]);
    (new R.assign 6 7 qTail node);
    (new R.main_unlock 7 8 lockT);

    (new R.kill_thread 8 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next';head'|]);
    (new R.main_lock 101 102 lockH);

    (new R.assign 102 103 head' qHead);
    (new R.atomic 103 104 [(new R.assign_dot_next 103 (-1) next' head');(new R.record_empty (-1) 104);]);

    (new R.equality 104 105 next' null);
    (new R.atomic 105 111 [(new R.main_unlock 105 (-1) lockH);(new R.validate_empty (-1) 111 "validateEmpty" ob);]);

    (new R.inequality 104 107 next' null);
    (new R.assign_return 107 108 next');
    (new R.atomic 108 109 [(new R.assign 108 (-1) qHead next');(new R.validate_delete (-1) 109 "delete" ob);]);
    (new R.main_unlock 109 110 lockH);

    (new R.free_cell 110 111 head');

    (new R.kill_thread 111 0);
  ]

end

module PriorityQueue_Buckets : Example.E = struct

  let name = "Coarse Priority Queue (with Buckets)"

  let qHeads = Array.map (fun i -> Label.global (i+3,("H"^(string_of_int i)))) [|0;1|]
  let qTails = Array.map (fun i -> Label.global (i+5, ("T"^(string_of_int i)))) [|0;1|]
  let null = Label.nil
  let node = Label.local (0,"n")
  let next' = Label.local (0,"next'")

  let initial_predicates ob =
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_priority_queue_buckets qHeads qTails interesting_colors 1

  let lock = 0

  let predicate_transformers ob =
    [
    (* ============================ enqueue =============================== *)
    (* enqueue high *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 2 node);
(*     (new R.data_assign_var 3 4 node v); *)
    (new R.dot_next_assign 2 4 node null);
    (new R.main_lock 4 5 lock);
    (new R.atomic 5 6 [(new R.dot_next_assign 5 (-1) qTails.(1) node);(new R.validate_insert (-1) 6 "insertHigh" ob node);]);
    (new R.assign 6 7 qTails.(1) node);
    (new R.main_unlock 7 8 lock);
    (new R.kill_thread 8 0);

    (* enqueue low *)
    (new R.atomic 0 11 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 11 (Observer.get_all_data ob));]);
    (new R.new_cell 11 12 node);
(*     (new R.data_assign_var 13 14 node v); *)
    (new R.dot_next_assign 12 14 node null);
    (new R.main_lock 14 15 lock);
    (new R.atomic 15 16 [(new R.dot_next_assign 15 (-1) qTails.(0) node);(new R.validate_insert (-1) 16 "insertLow" ob node); ]);
    (new R.assign 16 17 qTails.(0) node);
    (new R.main_unlock 17 18 lock);
    (new R.kill_thread 18 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next'|]);
    (new R.main_lock 101 102 lock);

    (new R.equality 102 103 qHeads.(1) qTails.(1)); (* high empty *)

    (new R.atomic 103 104 [(new R.equality 103 (-1) qHeads.(0) qTails.(0));(new R.record_empty (-1) 104);]); (* low empty *)
    (new R.atomic 104 1000 [(new R.main_unlock 104 (-1) lock);(new R.validate_empty (-1) 1000 "validateEmpty" ob);]);

    (new R.inequality 102 106 qHeads.(1) qTails.(1)); (* high not empty *)
    (new R.assign_dot_next 106 107 next' qHeads.(1));
    (new R.assign_return 107 108 next');
    (new R.atomic 108 109 [(new R.assign 108 (-1) qHeads.(1) next');(new R.validate_delete (-1) 109 "delete" ob)]);
    (new R.main_unlock 109 1000 lock);

    (new R.inequality 103 206 qHeads.(0) qTails.(0)); (* low not empty *)
    (new R.assign_dot_next 206 207 next' qHeads.(0));
    (new R.assign_return 207 208 next');
    (new R.atomic 208 209 [(new R.assign 208 (-1) qHeads.(0) next');(new R.validate_delete (-1) 209 "delete" ob)]);
    (new R.main_unlock 209 1000 lock);

    (new R.kill_thread 1000 0);
  ]
  
end

module PriorityQueue_ListBased : Example.E = struct

  let name = "Coarse Priority Queue (List-based)"

  let qHead = Label.global (3,"H")
  let qTailHigh = Label.global (4, "Thigh")
  let qTailLow = Label.global (5, "Tlow")
  let null = Label.nil
  let node = Label.local (0,"n")
  let next = Label.local (1,"next")
  let next' = Label.local (0,"next'")
  let head' = Label.local (1,"h'")

  let lock = 0

  let initial_predicates ob =
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_priority_queue_listbased qHead qTailHigh qTailLow interesting_colors 1

  let predicate_transformers ob =
    [
    (* ============================ enqueue =============================== *)
    (* enqueue high *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node;next|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 2 node);
    (new R.main_lock 2 3 lock);
    (new R.assign_dot_next 3 4 next qTailHigh);
    (new R.dot_next_assign 4 5 node next);
    (new R.dot_next_assign 5 6 qTailHigh node);
    (new R.atomic 6 7 [(new R.assign 6 (-1) qTailHigh node);(new R.validate_insert (-1) 7 "insertHigh" ob node);]);
    (new R.main_unlock 7 10 lock);
    (new R.kill_thread 10 0);

    (* enqueue low *)
    (new R.atomic 0 11 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 11 (Observer.get_all_data ob));]);
    (new R.new_cell 11 12 node);
    (new R.main_lock 12 13 lock);
    (new R.dot_next_assign 13 14 node null);
    (new R.dot_next_assign 14 15 qTailLow node);
    (new R.atomic 15 16 [(new R.assign 15 (-1) qTailLow node);(new R.validate_insert (-1) 16 "insertLow" ob node);]);
    (new R.main_unlock 16 20 lock);
    (new R.kill_thread 20 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next';head'|]);
    (new R.main_lock 101 102 lock);

    (new R.atomic 102 103 [(new R.assign_dot_next 102 (-1) next' qHead);(new R.record_empty (-1) 103);]);

    (new R.equality 103 105 next' null);
    (new R.atomic 105 200 [(new R.main_unlock 105 (-1) lock);(new R.validate_empty (-1) 200 "validateEmpty" ob);]);

    (new R.inequality 104 107 next' null);
    (new R.assign_return 107 108 next');
    (new R.equality 108 109 qHead qTailHigh);
    (new R.assign 109 110 qTailHigh next');
    (new R.inequality 108 110 qHead qTailHigh);
    (new R.atomic 110 111 [(new R.assign 110 (-1) qHead next');(new R.validate_delete (-1) 111 "delete" ob);]);
    (new R.main_unlock 111 200 lock);

    (new R.kill_thread 200 0);
  ]
  
end

module BucketLocksPriorityQueue : Example.E = struct

  let name = "Bucket locks Priority Queue"

  let qHeads = Array.map (fun i -> Label.global (i+3,("H"^(string_of_int i)))) [|0;1|]
  let qTails = Array.map (fun i -> Label.global (i+5, ("T"^(string_of_int i)))) [|0;1|]
  let null = Label.nil
  let node = Label.local (0,"n")
  let next' = Label.local (0,"next'")

  let initial_predicates ob =
    let interesting_colors = Array.of_list (List.filter Data.is_interesting (Observer.get_all_data ob)) in
    C.create_priority_queue_buckets qHeads qTails interesting_colors 2

  let lockLow = 0
  let lockHigh = 1

  let predicate_transformers ob =
    [
    (* ============================ enqueue =============================== *)
    (* enqueue high *)
    (new R.atomic 0 1 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 1 (Observer.get_all_data ob));]);
    (new R.new_cell 1 2 node);
(*     (new R.data_assign_var 3 4 node v); *)
    (new R.dot_next_assign 2 4 node null);
    (new R.main_lock 4 5 lockHigh);
    (new R.atomic 5 6 [(new R.dot_next_assign 5 (-1) qTails.(1) node);(new R.validate_insert (-1) 6 "insertHigh" ob node);]);
    (new R.assign 6 7 qTails.(1) node);
    (new R.main_unlock 7 8 lockHigh);
    (new R.kill_thread 8 0);

    (* enqueue low *)
    (new R.atomic 0 11 [(new R.init_thread 0 (-1) [|node|]);(new R.record_insert (-1) 11 (Observer.get_all_data ob));]);
    (new R.new_cell 11 12 node);
(*     (new R.data_assign_var 13 14 node v); *)
    (new R.dot_next_assign 12 14 node null);
    (new R.main_lock 14 15 lockLow);
    (new R.atomic 15 16 [(new R.dot_next_assign 15 (-1) qTails.(0) node);(new R.validate_insert (-1) 16 "insertLow" ob node); ]);
    (new R.assign 16 17 qTails.(0) node);
    (new R.main_unlock 17 18 lockLow);
    (new R.kill_thread 18 0);

    (* ============================ dequeue =============================== *)
    (new R.init_thread 0 101 [|next'|]);
    (new R.main_lock 101 102 lockHigh);
    (new R.main_lock 103 104 lockLow);

    (new R.equality 104 105 qHeads.(1) qTails.(1)); (* high empty *)

    (new R.atomic 105 106 [(new R.equality 105 (-1) qHeads.(0) qTails.(0));(new R.record_empty (-1) 106);]); (* low empty *)
    (new R.atomic 106 107 [(new R.main_unlock 106 (-1) lockLow);(new R.validate_empty (-1) 107 "validateEmpty" ob);]);
    (new R.main_unlock 107 1000 lockHigh);

    (new R.inequality 104 110 qHeads.(1) qTails.(1)); (* high not empty *)
    (new R.assign_dot_next 110 111 next' qHeads.(1));
    (new R.assign_return 111 112 next');
    (new R.atomic 112 113 [(new R.assign 112 (-1) qHeads.(1) next');(new R.validate_delete (-1) 113 "delete" ob)]);

    (new R.main_lock 113 114 lockLow);
    (new R.main_unlock 114 1000 lockHigh);

    (new R.inequality 105 206 qHeads.(0) qTails.(0)); (* low not empty *)
    (new R.assign_dot_next 206 207 next' qHeads.(0));
    (new R.assign_return 207 208 next');
    (new R.atomic 208 209 [(new R.assign 208 (-1) qHeads.(0) next');(new R.validate_delete (-1) 209 "delete" ob)]);

    (new R.main_lock 209 210 lockLow);
    (new R.main_unlock 210 1000 lockHigh);

    (new R.kill_thread 1000 0);
  ]
  
end

