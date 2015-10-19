open Printf

let _ = 

  Debug.print "%s DEBUG %s\n" Debug.red Debug.noColor;

  let c = Constraint.create_queue ([|"#";"_";"H";"T"|],[|"n";"t";"next";"h'";"t'";"next'";"v"|]) in

  Constraint.to_dot c "tmp/queue";

  let c' = Constraint.create_stack ([|"#";"_";"S"|],[|"n";"t";"t'";"x'";|]) in

  Constraint.to_dot c' "tmp/stack";

  Debug.print "%s DEBUG %s\n" Debug.red Debug.noColor;

;;

(* module P = Constraint *)
(* module T = Rule *)
(* module PS = Minset.KeyBased(P) *)

(* exception Dead *)
(* exception ClashWithInit of P.t *)

(* let runSequence _ = begin *)

(*   let ob = Example.TreiberABA.observer "loss" in *)

(*   let x = Label.local "x" *)
(*   and t = Label.local "t" *)
(*   and x' = Label.local "x'" *)
(*   and t' = Label.local "t'" *)
(*   and s = Label.global "S" *)
(*   and res' = Label.local "res'" *)
(*   and v = Label.local "v" *)
(*   in *)

(*   let pop = new T.atomic 17 18 [(new T.cas_success 17 (-1) s t' x');(new T.validate_delete (-1) 18 "delete" res' ob);] in *)
(*   let free = new T.free_cell 18 19 t' in *)
(*   let newCell = new T.new_cell 1 3 x ~gc:false in *)
(*   let data_assign = new T.data_assign_var 3 4 x v in *)
(*   let assign = new T.assign 4 5 t s in *)
(*   let redirect = new T.dot_next_assign 5 6 x t in *)
(*   let push = new T.atomic 6 7 [(new T.cas_success 6 (-67) s t x);(new T.validate_insert (-67) 7 "insert" ob);] in *)

(*   let transformers = [ pop; free; push(\* R *\); newCell; data_assign; assign; redirect; push(\* W *\) ] in *)
(*   let patterns = P.test_create_patterns () in *)

(*   let interferers = List.map2 (fun t p -> *)
(*     P.log_message p (sprintf "precondition for %s" (T.string_of t)); *)
(*     P.to_dot p (sprintf "tmp/pattern-%d" (P.id p)); *)
(*     p,t) transformers patterns *)
(*   in *)
(*   let start = P.test_create () in *)

(*   let system = PS.create () in *)
(*   ignore( PS.insert system start ); *)

(*   let w = Queue.create () in *)
(*   Queue.add start w; *)
(*   let step = ref 0 in *)
(*   let runInterference current = begin *)

(*     try *)
(*     let renamed_current = P.rename (P.shape current) in *)
    
(*     List.iter (fun (interferer,r) -> begin *)
(*       let info_interferer = P.info interferer in *)
(*       match P.meet renamed_current (P.shape interferer) (P.pc interferer) with *)
(*       | [] -> () *)
(*       | mList ->  *)
(* 	  List.iter (fun shape -> begin *)
(* 	    let m = P.recombine shape info_interferer in *)
(* 	    Debug.print "--------------------------------\n"; *)
(* 	    Debug.print "Interferer: %s\n" (P.string_of interferer); *)
(* 	    Debug.print "Rule: %s\n" (T.string_of r); *)
(* 	    Debug.print "Meet: %d\n" !step; *)
(* 	    P.to_dot m (sprintf "tmp/_step/%d-meet" !step); *)
(* 	    incr step; *)
(* 	    let post = r#post m in *)
(* 	    List.iter (fun (pp,_) -> begin *)
(* 	      if not(P.is_alive current) then raise Dead; *)
(* 	      let shape = P.project (P.shape pp) (P.pc pp) in *)
(* 	      let observer = P.observer pp in *)
(* 	      let info = P.info current in *)
(* 	      let info' = P.Info.clone info in *)
(* 	      P.Info.set_observer observer info'; *)
(* 	      let p = P.recombine shape info' in *)
(* 	      Debug.print "After interference: %d\n" (P.id p); *)
(* 	      P.set_parent p current; *)
(* 	      P.log_message p (sprintf "interference on %d with interferer %d rule %s\\ngives %d" (P.id current) (P.id interferer) (T.string_of r) (P.id p)); *)
(* 	      P.to_dot p (sprintf "tmp/_step/%d-interference" (P.id p)); *)
(* 	      match PS.insert system p with  *)
(* 	      |	true,_ -> *)
(*  		  Debug.print "Insertion of %d\n" (P.id p); *)
(* 		  Queue.add p w *)
(* 	      | _ -> () *)
(* 	    end) post *)
(* 	  end) mList; *)
(*     end) interferers; *)
(*     with Dead -> () *)
(*   end in *)

(*   let rec loop _ = begin *)
(*     try  *)
(*       let current = Queue.take w in *)
(*       Debug.print "\n==================================\n"; *)
(*       Debug.print "I pick %s\n" (P.string_of current); *)
(*       P.to_dot current (sprintf "tmp/%d" (P.id current)); *)
(*       if Observer.is_bad (P.observer current) then raise (ClashWithInit current); *)
(*       Debug.level (1); *)
(*       runInterference current; *)
(*       Debug.level (-1); *)
(*       loop () *)
(*     with Queue.Empty -> () *)
(*     | ClashWithInit p -> *)
(* 	P.to_dot p "tmp/clash"; *)
(* 	P.iter_trace p (fun p' -> P.to_dot p' (sprintf "tmp/_debug/trace-%d" (P.id p'))); *)
(* 	Debug.print "\n%s Clashing! %s observed a bad trace %s\n" Debug.red (P.string_of p) Debug.noColor; *)
(* 	failwith("Houston, we have a problem!"); *)
(*   end in *)
(*   loop (); *)

(* end *)

(* let _ =  *)

(*   ignore( Sys.command("mkdir -p tmp/_step") ); *)
(*   ignore( Sys.command("mkdir -p tmp/_debug") ); *)
  
(*   runSequence (); *)
(* ;; *)
