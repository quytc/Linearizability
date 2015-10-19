module C = Constraint
module R = Rule

(*=============================================RDCSS=============================================*)
module Reset : Example.E = struct
   let name = "RDCSS"	
   let a = Label.global (3,"A",1)
   let null = Label.nil
   let free = Label.free
   let d = Label.local (0, "d",1)
   let o = Label.local (1, "o",1)
   let n = Label.local (2, "n",1)
   let r = Label.local (3, "r",1)
   let c = Label.local (4, "c",1)
   let e = Label.local (5, "e",1)
   
  let initial_predicates  = 
   C.create_ccas a 
	 let predicate_transformers  =
	[			  
   (new R.init_thread 0 (1) [|d;o;n;r;c;e|]);  
    (new R.atomic 1 7 [(new R.in_equality 1 (-1) a o);(new R.data_inequality (-1) (-3) a 2);(new R.validate_unsuccess_ccas (-3) 7 o a)]);
     (new R.atomic 1 3 [(new R.create_desc_rdcss 1 2 d a o n c e); ]);	
     (new R.atomic 3 4 [(new R.ccas_success 3 4 r a o d); ]);
     (*Complate d*)
     (new R.atomic 4 7 [(new R.ccas_success_new 4 (-7) a d);(new R.validate_ccas (-7) 4 o a)]);
     (new R.atomic 4 7 [(new R.ccas_success_old 4 (-7) a d);(new R.validate_ccas (-7) 4 o a)]);
    
	 (new R.atomic 3 8 [(new R.ccas_fail 3 8 r a o d);]);
	 (new R.atomic 8 9 [(new R.data_equality 8 9 r 2);]);
	 (*Help this guy to complete*)
	 (new R.atomic 9 3 [(new R.ccas_help_success_new 9 (-3) a r);(new R.validate_help_ccas (-3) 4 r a)]);
     (new R.atomic 9 3 [(new R.ccas_help_success_old 9 (-3) a r);(new R.validate_help_ccas (-3) 4 r a)]);
     (*Read RDCSS*)  
     (new R.atomic 1 10 [(new R.data_equality 1 10 a 2);]);
	 (*Help this guy to complete*)
	 (new R.atomic 10 1 [(new R.ccas_help_success_new 10 (-1) a a);(new R.validate_help_ccas (-1) 1 a a)]);
     (new R.atomic 10 1 [(new R.ccas_help_success_old 10 (-1) a a);(new R.validate_help_ccas (-1) 1 a a)]);
  
	 (new R.kill_thread 7 0);					 
     (new R.kill_thread 8 0);				  
	 ]
end   



