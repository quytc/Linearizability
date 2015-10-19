type obs = Init | T | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S1' | S2' | Bad | Happy
type help = {pc:int list; op: int; ret: bool; ord: int}
type ret = {cnt:int; add:int; rmv:int}
val maxID: int ref
(*val scount: int ref*)

(** {6 Generic interface} *)

  type t



  val id: t -> int
 
 
(*   val iter_trace: t -> (t -> unit) -> unit *)

(** [clone c] returns a new copy of c, copying the shape too. *)
  val clone: t -> t

  val pc: t -> int -> int
	val bound: t -> int
	val interf_pc: t -> int -> int
  val set_pc: t -> int -> int -> unit
  val nthreads: t -> int
	(*val extract_from_star: t -> int -> t*t*)
  val observer: t -> obs
  val set_observer: t -> obs -> unit
  val abstract_away: t  -> int -> int -> t -> t
  val abstract_away_p2: t  -> int -> int -> t -> t
    
  val in_queue: t -> bool
  val not_in_happy: t -> bool
    val not_in_s2: t -> bool  
    val set_in_queue: t -> bool -> unit
    val set_helper: t -> bool -> unit
	val set_interested: t -> bool -> unit
	val interested: t -> bool
 val check_commit: t list -> t list
  exception IgnoreConstraint
  exception NullPointerDereferencing of t * (string Lazy.t)
  exception DoubleFree of t * (string Lazy.t)
  exception Dangling of t * (string Lazy.t)
  exception FreeDereferencing of t * (string Lazy.t)
  exception Cycle of t * (string Lazy.t)
  exception ClashWithInit of t

	val gvar:t->int
	val copy: t -> t -> t -> t
	val var:t->int
	  val create_set: Label.t -> Label.t -> Label.t -> t list
   	val create_lock_set: Label.t -> Label.t -> t list
    val create_unordered_set: Label.t -> Label.t -> Label.t -> t list
     
    val create_elim_stack: Label.t -> Label.t -> Label.t -> t list
    val create_stack: Label.t -> t list
    val create_queue: Label.t -> Label.t  -> t list
     
    val create_twolock_queue: Label.t -> Label.t -> Label.t -> Label.t  -> t list
    val strengthen_data_assign_unordered:  Label.t -> t -> int -> t list
	  
	  val create_hw_queue: Label.t -> Label.t -> t list
    val init_thread: Label.t array -> t -> int -> t list
	  val do_intersection: t -> t -> int -> int -> int -> int -> t list * bool
 		val do_full_intersection: t -> t -> int -> t list * bool
    val emp_constraint: t
	  val start_point: t -> int
	  val kill_variable : Label.t -> t -> int -> t list
	  val kill_variable_index : int -> t -> int -> t list
		val invert_lock_constraint: t -> t	
    val kill_thread: t -> int -> t list
    val assign: Label.t -> Label.t -> t -> int -> t list
	  val data_exchange: Label.t -> Label.t -> t -> int -> t list
		
	  val reach: Label.t -> Label.t -> t -> int -> t list
	
		val unreach: Label.t -> Label.t -> t -> int -> t list
	
	
	  val reach_one: Label.t -> Label.t -> t -> int -> t list  
	  val dot_next_assign: Label.t -> Label.t -> t -> int -> t list
    val dot_next_assign_alone: Label.t -> Label.t -> t -> int -> t list
    val color_var_equality:    Label.t -> Label.t -> t -> int -> t list
    val color_var_inequality:    Label.t -> Label.t -> t -> int -> t list
 
   	val filter_dot_next_assign: Label.t -> Label.t -> t -> int -> t list
    val get_marked_assign_dot_next:Label.t -> Label.t -> Label.t -> t -> int -> t list
    val validate_ex_push_pop:Label.t ->t -> int -> t list
    val var_equality:Label.t -> int -> t -> int -> t list
    val validate_pop:Label.t -> t -> int -> t list
	  val validate_pop_empty:Label.t -> t -> int -> t list
	
    val nothing: t -> int -> t list
	  val empty: t -> int -> t list
	  val hq_deq_strengthen: Label.t -> t -> int -> t list
	  val validate_ex_enqueue_dequeue:t -> int -> t list
    val validate_push:Label.t -> t -> int -> t list
    val validate_enqueue:Label.t -> t -> int -> t list
	
	  val validate_call_enqueue:Label.t -> t -> int -> t list
	  val validate_ret_enqueue:Label.t -> t -> int -> t list
		val validate_ret_dequeue:Label.t -> t -> int -> t list
		
    val validate_dequeue:Label.t -> t -> int -> t list
	
	  val validate_dequeue_empty:Label.t -> t -> int -> t list
		
		val mark_assign:Label.t -> int -> t -> int -> t list
		val strengthen_mark_assign:Label.t -> int -> t -> int -> t list
   (*
  val validate_insert:Label.t -> int list -> bool -> t -> int -> t list
      *)
	  val validate_insert_unordered:Label.t -> int list -> bool -> t -> int -> t list
	
    val validate_return:int -> bool -> t -> int -> t list
     
    val validate_return_new:int -> Label.t -> bool -> t -> int -> t list
     
	  val validate_insert:Label.t -> bool ->  help list ->t -> int -> t list
	
    val validate_uninsert:Label.t ->  t -> int -> t list  
    val validate_undelete:Label.t ->  t -> int -> t list    
      
    val validate_fixed_uninsert:Label.t -> t -> int -> t list  
    val validate_fixed_undelete:Label.t -> t -> int -> t list    
      
   (* 
	  val validate_delete:Label.t ->  int list -> bool ->t -> int -> t list
    *)
		
		val result: string
	      
	  val validate_delete_unordered:Label.t ->  int list -> bool ->t -> int -> t list
	
    val validate_delete:Label.t -> bool ->  help list ->t -> int -> t list
	
    val validate_contains: Label.t -> bool -> t -> int -> t list
      
       val validate_contains_local: Label.t -> bool -> t -> int -> t list
       val create_ccas: Label.t -> t list
       
         
          val validate_ccas:Label.t -> Label.t -> t -> int -> t list 
      val validate_unsuccess_ccas:Label.t -> Label.t -> t -> int -> t list 
   val validate_help_ccas:Label.t -> Label.t -> t -> int -> t list         
     
     
     val ccas_success:  Label.t -> Label.t -> Label.t -> Label.t -> t -> int -> t list
  val ccas_fail:  Label.t -> Label.t -> Label.t -> Label.t -> t -> int -> t list
				
	val ccas_success_new:  Label.t -> Label.t -> t -> int -> t list
		val ccas_success_old:  Label.t -> Label.t -> t -> int -> t list
		
		val ccas_help_success_new:  Label.t -> Label.t -> t -> int -> t list
		val ccas_help_success_old:  Label.t -> Label.t -> t -> int -> t list
			
	val create_desc:  Label.t -> Label.t -> Label.t -> t -> int -> t list
	val create_desc_rdcss:  Label.t -> Label.t -> Label.t ->  Label.t -> Label.t -> Label.t -> t -> int -> t list
     
       
           
    val validate_contains_new: Label.t -> bool -> help list -> t -> int -> t list
    val validate_contains_alone_new: Label.t -> bool -> help list -> t -> int -> t list
	  val validate_contains_alone_true: Label.t -> bool -> help list -> t -> int -> t list
    val validate_fixed_contains: bool -> t -> int -> t list  
  
  val validate_early_contains: bool -> t -> int -> t list
	 val validate_contains_alone: bool -> t -> int -> t list
  val red_seen: t -> int -> t list
  val red_not_seen: t -> int -> t list	
  val var_inequality:Label.t -> int -> t -> int -> t list
		
 val get_scope: Label.t -> t -> int -> int		
		
  val assign_dot_next: Label.t -> Label.t -> t -> int -> t list
  val assign_self_dot_next: Label.t -> t -> int -> t list
	
  val assign_dot_next_prev: Label.t -> Label.t -> t -> int -> t list
  val make_new_cell: Label.t -> t -> int -> t list
  
  val global_lock: Label.t -> t -> int -> t list
    val global_unlock: Label.t -> t -> int -> t list
      
  val next_equality: Label.t -> Label.t -> t -> int -> t list
  val next_inequality: Label.t -> Label.t -> t -> int -> t list
  val equality: Label.t -> Label.t -> t -> int -> t list
    
  val insert_elim: Label.t -> Label.t -> t -> int -> t list
    
  val data_assign:Label.t -> int -> t -> int -> t list
  val op_assign:Label.t -> int -> t -> int -> t list
  val elim_data_assign:Label.t -> Label.t -> t -> int -> t list 
  val get_him_success:Label.t ->Label.t ->Label.t -> t -> int -> t list
  val get_him_fail:Label.t ->Label.t ->Label.t-> t -> int -> t list
	 val cas_data_elim_fail:  Label.t -> int -> int -> t -> int -> t list
  	 val cas_data_fail:  Label.t -> int -> int -> t -> int -> t list  
	val create_elim_queue: Label.t -> Label.t -> Label.t -> t list
	
    
     val cas_data_elim_success:  Label.t -> int -> int -> t -> int -> t list
       
     val strengthen_op_assign:  Label.t -> t -> int -> t list
       
  val strengthen_cas_data_elim_success:  Label.t -> int -> int -> t -> int -> t list		
	   val op_equality:    Label.t -> int -> t -> int -> t list
   val strengthen_cas_data_success:  Label.t -> int -> int -> t -> int -> t list		
	  
  val op_inequality:    Label.t -> int -> t -> int -> t list
  
 
   val var_data_assign: Label.t -> Label.t -> t -> int -> t list
	val color_assign:Label.t -> int -> t -> int -> t list
		val color_assign_variable:Label.t -> Label.t -> t -> int -> t list
  val data_equality:    Label.t -> int -> t -> int -> t list
	val is_data_equality: Label.t -> int -> t -> int -> t list
 val color_equality: Label.t -> int -> t -> int -> t list
 val color_inequality: Label.t -> int -> t -> int -> t list
 val is_global: Label.t -> t -> bool
     val is_color_equality: Label.t -> int -> t -> int -> t list
  val set_example_name: string -> unit  
	
		  val set_property_name: string -> unit  	
				
	  val hq_unnull_node: Label.t  -> t -> int -> t list
		  val hq_null_node: Label.t  -> t -> int -> t list
    val data_equality_variable: Label.t -> Label.t -> t -> int -> t list 
      
   	val data_inequality_variable: Label.t -> Label.t -> t -> int -> t list    
   	val data_assign_variable: Label.t -> Label.t -> t -> int -> t list        
  val data_inequality: Label.t -> int ->t -> int -> t list
	val signature: t -> string
	val test:t -> bool
	val elim:t -> bool
	val test2:t -> bool
 val set_flag:t -> int -> int -> t list
 val kill_flag:t -> int -> t list
      val kill_ret:t -> int -> t list
		val test3:t -> bool
	val compare_constraint:t -> t -> bool
	val ord_two_cells: t -> int -> int -> int
	val compare_matrix: t -> (int array) array
	val merge_constraint: t -> t -> t*bool
	val assign_constraint: t -> t -> unit
	val compute_successor: t -> unit
	val successor: t -> (int, int) Hashtbl.t
	val less_than: Label.t -> Label.t -> t -> int -> t list
	val equal: Label.t -> Label.t -> t -> int -> t list
 	val in_equal: Label.t -> Label.t -> t -> int -> t list
 val is_less_than: Label.t -> Label.t -> t -> int -> t list
   val not_less_than: Label.t -> Label.t -> t -> int -> t list
	val equal_red: Label.t -> t -> int -> t list	
	
		val canbe_red: Label.t ->Label.t ->Label.t -> t -> int -> t list	
	
	val in_equality: Label.t -> Label.t -> t -> int -> t list
	val pure_strengthen: t -> unit
	val attempt_mark:  Label.t -> Label.t -> int -> t -> int -> t list
	val strengthen_mark:  Label.t -> Label.t -> int -> t -> int -> t list
   
 val filter_mark:  Label.t -> Label.t -> int -> t -> int -> t list
 val filter_cas_set:  Label.t -> Label.t -> int -> t -> int -> t list

 val filter_dcas_set:  Label.t -> Label.t -> Label.t -> t -> int -> t list

 	val ord_two_cells: t -> int -> int -> int

  val attempt_mark_fail:  Label.t -> Label.t ->int -> t -> int -> t list
  val dot_next_unmarked_equality:  Label.t -> Label.t -> t -> int -> t list
  val in_dot_next_unmarked_equality:  Label.t -> Label.t -> t -> int -> t list
  val strengthen_dot_next_unmarked_equality:  Label.t -> Label.t -> t -> int -> t list  
  val cas_success_set:  Label.t -> Label.t -> int -> Label.t -> t -> int -> t list
	
	val dcas_success_set:  Label.t -> Label.t -> Label.t -> Label.t -> t -> int -> t list
	
  val cas_success:  Label.t -> Label.t -> Label.t -> t -> int -> t list
  val cas_data_success:  Label.t -> int -> int -> t -> int -> t list
	
	  val cas_multi_set_success:  Label.t -> int -> int -> t -> int -> t list
	
	val cas_fail:  Label.t -> Label.t -> Label.t -> t -> int -> t list
   
   val cas_next_success:  Label.t -> Label.t -> Label.t -> t -> int -> t list
	val cas_next_fail:  Label.t -> Label.t -> Label.t -> t -> int -> t list
   
	val cas_success_set_mark:  Label.t -> Label.t -> int -> Label.t -> t -> int -> t list
	val strengthen_cas_success_set:  Label.t -> Label.t -> int -> Label.t -> t -> int -> t list
	
		val strengthen_dcas_success_set:  Label.t -> Label.t -> Label.t -> Label.t -> t -> int -> t list
	
 val strengthen_cas_success:  Label.t -> Label.t -> Label.t -> t -> int -> t list
 val strengthen_cas_next_success:  Label.t -> Label.t -> Label.t -> t -> int -> t list
   val strengthen_fail:  Label.t -> Label.t -> Label.t -> t -> int -> t list
	val strengthen_cas_success_set_mark:  Label.t -> Label.t -> int -> Label.t -> t -> int -> t list
	val cas_fail_set:  Label.t -> Label.t -> int -> Label.t -> t -> int -> t list
	
		val dcas_fail_set:  Label.t -> Label.t -> Label.t -> t -> int -> t list
	val clean: t-> unit	
	val print_cons: t-> unit
  val print_merge_cons: t->t->t-> unit
  val push_to_highway: t -> int -> t
	
  val lock_acquire_success: Label.t -> int -> bool -> t -> int -> t list
	
  val lock_acquire_fail: Label.t -> int -> t -> int -> t list
	
	val lock_release_success: Label.t -> int -> bool -> t -> int -> t list
	
	val lock_release_fail: Label.t -> int -> t -> int -> t list
	
	val strengthen_lock_acquire: Label.t -> int -> t -> int -> t list
	
	val strengthen_dot_next_assign_lock: Label.t -> Label.t -> t -> int -> t list
		val strengthen_dot_next_assign: Label.t -> Label.t -> t -> int -> t list
	val strengthen_lock_release: Label.t -> int -> t -> int -> t list
	
	val dot_next_assign_lock: Label.t -> Label.t ->  t -> int -> t list
	val dot_next_assign_lock_fail: Label.t -> Label.t -> t -> int -> t list