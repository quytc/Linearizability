  type cons = Constraint.t
   type help = Constraint.help 
  class type transformer =
    object
      method post: cons -> int -> cons list
      method post_interf: cons -> int -> cons list
      method strengthen: cons -> int -> cons list
        method filter: cons -> int -> cons list
      method is_interf: bool
			method is_interfed: bool
      method toString: string
      method fromPC: int
      method toPC: int
    end
	
  type t = transformer

  val post: t -> cons -> cons list
  val strengthen: t -> cons -> cons list
  val filter: t -> cons -> cons list
  val post_interf : t -> cons -> cons list
  val is_interf: t -> bool
	val name: t -> string
  val is_interfed: t -> bool


(** A concrete transformer [x := y] *)
  class assign: int -> int -> Label.t -> Label.t -> transformer
  class data_exchange: int -> int -> Label.t -> Label.t -> transformer
 class reach: int -> int -> Label.t -> Label.t -> transformer

 class unreach: int -> int -> Label.t -> Label.t -> transformer

 class reach_one: int -> int -> Label.t -> Label.t -> transformer
 class color_var_equality: int -> int -> Label.t -> Label.t -> transformer
	class color_var_inequality: int -> int -> Label.t -> Label.t -> transformer
	

(** A concrete transformer [x := y.next] *)
    class dot_next_assign: int -> int -> Label.t -> Label.t -> transformer
      class dot_next_assign_local: int -> int -> Label.t -> Label.t -> transformer
     class dot_next_assign_alone: int -> int -> Label.t -> Label.t -> transformer
     class data_assign_unordered: int -> int -> Label.t -> int -> transformer   
        
      
      class assign_dot_next: int -> int -> Label.t -> Label.t -> transformer
      
       class assign_self_dot_next: int -> int -> Label.t -> transformer
    
      class assign_dot_next_prev: int -> int -> Label.t -> Label.t -> transformer
(** A concrete transformer [x := new_cell()] *)
  class new_cell: int -> int -> ?gc:bool -> Label.t -> transformer
    class global_lock: int -> int -> Label.t -> transformer
      
      class global_unlock: int -> int -> Label.t -> transformer
      
  class next_equality: int -> int -> Label.t -> Label.t -> transformer
	class next_inequality: int -> int -> Label.t -> Label.t -> transformer
	
  class equality: int -> int -> Label.t -> Label.t -> transformer
  class nothing: int -> int -> transformer
	class less_than: int -> int -> Label.t -> Label.t -> transformer
  
   	class equal: int -> int -> Label.t -> Label.t -> transformer
   	class in_equal: int -> int -> Label.t -> Label.t -> transformer

		class equal_red: int -> int -> Label.t -> transformer	
		
				class canbe_red: int -> int -> Label.t -> Label.t -> Label.t -> transformer	
				
			class lock_acquire_success: int -> int -> Label.t -> int -> transformer
	class lock_acquire_fail: int -> int -> Label.t -> int -> transformer
	
		class dot_next_assign_lock: int -> int -> Label.t -> Label.t -> transformer
		class dot_next_assign_lock_fail: int -> int -> Label.t -> Label.t -> transformer	
	
			class kill_variable: int -> int -> Label.t  -> transformer

	class lock_release_success: int -> int -> Label.t -> int -> transformer
	class lock_release_fail: int -> int -> Label.t -> int -> transformer
	class data_equality_variable: int -> int -> Label.t -> Label.t -> transformer

	class data_inequality_variable: int -> int -> Label.t -> Label.t -> transformer
   
   
   class data_assign_variable: int -> int -> Label.t -> Label.t -> transformer
      
   
   class data_assign: int -> int -> Label.t -> int -> transformer
     class op_assign: int -> int -> Label.t -> int -> transformer
       class elim_data_assign: int -> int -> Label.t -> Label.t -> transformer  
       class var_data_assign: int -> int -> Label.t-> Label.t -> transformer
     
         class color_assign: int -> int -> Label.t -> int -> transformer
     
           class color_assign_variable: int -> int -> Label.t -> Label.t -> transformer
                 
		class data_equality:  int -> int-> Label.t -> int -> transformer
       class color_equality:  int -> int-> Label.t -> int -> transformer
			
			
			       class is_color_equality:  int -> int-> Label.t -> int -> transformer
			
			
     class color_inequality:  int -> int-> Label.t -> int -> transformer
          class op_equality:  int -> int-> Label.t -> int -> transformer
 
  class op_inequality:  int -> int-> Label.t -> int -> transformer
     
	  class hq_unnull_node:  int -> int-> Label.t  -> transformer
		  class hq_null_node:  int -> int-> Label.t  -> transformer
  class data_inequality:  int -> int -> Label.t -> int -> transformer
	
	class var_equality:  int -> int-> Label.t -> int -> transformer
   
   class set_flag: int -> int -> int  -> transformer
     
     class kill_flag: int -> int  -> transformer
       class get_him_success: int -> int -> Label.t -> Label.t -> Label.t -> transformer
	class get_him_fail:    int -> int -> Label.t -> Label.t -> Label.t -> transformer
	 class cas_data_elim_fail: int -> int -> Label.t -> int  -> int -> transformer         
    
    class cas_data_fail: int -> int -> Label.t -> int  -> int -> transformer         
      class insert_elim: int -> int ->  Label.t -> Label.t -> transformer 
        class cas_data_elim_success: int -> int -> Label.t -> int  -> int -> transformer         
  
          class kill_ret: int -> int  -> transformer
      (*
    class validate_insert:  int -> int-> Label.t -> int list -> bool -> transformer
      *)
		    class validate_insert_unordered:  int -> int-> Label.t -> int list -> bool -> transformer
		
        class validate_return:  int -> int-> int -> bool -> transformer
          
          class validate_return_new:  int -> int-> int -> Label.t -> bool -> transformer
          
	   class validate_insert:  int -> int-> Label.t -> bool -> help list -> transformer
	
     class validate_uninsert:  int -> int-> Label.t-> transformer
         class validate_undelete:  int -> int-> Label.t-> transformer
          
          class validate_fixed_uninsert:  int -> int-> Label.t-> transformer
         class validate_fixed_undelete:  int -> int-> Label.t-> transformer
       
                 (*
            class validate_delete:  int -> int-> Label.t -> int list -> bool -> transformer
              *)
                 class validate_delete_unordered:  int -> int-> Label.t -> int list -> bool -> transformer
	        class validate_delete:  int -> int-> Label.t -> bool -> help list -> transformer
   class validate_contains_new:  int -> int -> Label.t -> bool -> help list -> transformer
  class validate_contains_alone_true:  int -> int -> Label.t -> bool -> help list -> transformer	
	  class validate_contains_alone_new:  int -> int -> Label.t -> bool -> help list -> transformer
     class validate_contains:  int -> int -> Label.t -> bool -> transformer
	
	class validate_contains_local:  int -> int -> Label.t -> bool -> transformer
	class validate_ccas:  int -> int-> Label.t-> Label.t -> transformer  
         class validate_unsuccess_ccas:  int -> int-> Label.t-> Label.t -> transformer     
         class validate_help_ccas:  int -> int-> Label.t-> Label.t -> transformer     
           
           class ccas_success: int -> int -> Label.t -> Label.t -> Label.t  -> Label.t-> transformer   
	class ccas_fail: int -> int -> Label.t -> Label.t -> Label.t  -> Label.t-> transformer   
			
		    class ccas_success_new: int -> int ->  Label.t  -> Label.t-> transformer 
				    class ccas_success_old: int -> int -> Label.t  -> Label.t-> transformer 	

				    class ccas_help_success_new: int -> int ->  Label.t  -> Label.t-> transformer 
				    class ccas_help_success_old: int -> int -> Label.t  -> Label.t-> transformer 			
										
		     class create_desc: int -> int -> Label.t -> Label.t -> Label.t  -> transformer 
         class create_desc_rdcss: int -> int -> Label.t -> Label.t -> Label.t -> Label.t -> Label.t -> Label.t  -> transformer 
           		
           
      class validate_fixed_contains:  int -> int -> bool -> transformer
    
     class validate_early_contains:  int -> int -> bool -> transformer
    
   class validate_contains_alone:  int -> int -> bool -> transformer   
   class red_seen:  int -> int -> transformer
   class red_not_seen:  int -> int -> transformer		
   class validate_push:  int -> int-> Label.t -> transformer	
	 class validate_ex_enqueue_dequeue:  int -> int -> transformer   
    class validate_ex_push_pop:  int -> int-> Label.t -> transformer   
   class validate_pop:  int -> int-> Label.t -> transformer
	 class validate_pop_empty:  int -> int-> Label.t -> transformer
   class validate_enqueue:  int -> int-> Label.t -> transformer
	
	 class validate_call_enqueue:  int -> int-> Label.t -> transformer
	 class validate_ret_enqueue:  int -> int-> Label.t -> transformer
	 class validate_ret_dequeue:  int -> int-> Label.t -> transformer
	
   class validate_dequeue:  int -> int-> Label.t -> transformer
	 class validate_dequeue_empty:  int -> int-> Label.t -> transformer
	 class var_inequality:  int -> int -> Label.t -> int -> transformer				
			
	class in_equality: int -> int -> Label.t -> Label.t -> transformer

  class init_thread: int -> int -> Label.t array -> transformer
  class kill_thread: int -> int -> transformer

  class atomic: int -> int -> transformer list -> transformer
  class cond: int -> int -> transformer list -> transformer
    
  class get_marked_assign_dot_next: int -> int -> Label.t -> Label.t -> Label.t -> transformer

  class attempt_mark: int -> int -> Label.t -> Label.t-> int -> transformer
	class attempt_mark_fail: int -> int -> Label.t -> Label.t-> int -> transformer
   class cas_success_set: int -> int -> Label.t -> Label.t -> int -> Label.t -> transformer
  
	  class dcas_success_set: int -> int -> Label.t -> Label.t -> Label.t -> Label.t -> transformer
		   
     class dot_next_unmarked_equality: int -> int -> Label.t -> Label.t -> transformer
       class in_dot_next_unmarked_equality: int -> int -> Label.t -> Label.t -> transformer
    class cas_data_success: int -> int -> Label.t -> int  -> int -> transformer   
		       
    
		    
	class cas_success: int -> int -> Label.t -> Label.t  -> Label.t -> transformer
   class cas_fail: int -> int -> Label.t -> Label.t  -> Label.t -> transformer	
   class cas_next_success: int -> int -> Label.t -> Label.t  -> Label.t -> transformer
	class cas_next_fail: int -> int -> Label.t -> Label.t  -> Label.t -> transformer	  
		class cas_success_set_mark: int -> int -> Label.t -> Label.t -> int -> Label.t -> transformer
	class cas_fail_set: int -> int -> Label.t -> Label.t -> int -> Label.t -> transformer
	
		class dcas_fail_set: int -> int -> Label.t -> Label.t -> Label.t -> transformer