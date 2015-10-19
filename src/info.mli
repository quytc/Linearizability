
type t
type alpha
type beta

val none: t
val equal: t

val create_cell: int -> alpha -> beta -> t
val get_none_ord: t -> int
val intersect_lock: int -> int -> (int*int)
val dot_next_assign: int -> t
val update_none_ord: t -> int -> t
val update_label: t -> alpha -> beta -> t
val is_none: t -> bool
val is_none_no_ord: t -> bool
val is_none_ord: t -> bool
val is_equal: t -> bool
val is_reach: t -> bool
  
val is_reach2: t -> bool  
val is_reach1: t -> bool    
val is_reach_one: t -> bool
val is_reach_more: t -> bool
val get_alpha: t -> alpha
val get_beta: t -> beta
val get_relation: t -> int
val merge_cell: t -> t -> t*bool
val intersect_beta_elim: t -> t -> beta
val intersect_alpha_beta_elim: t -> t -> int -> int -> (int*int)-> alpha*int*int*(int*int)
  
val remove_color:t -> t
val compare_cell: t -> t -> bool
val unfold_single_cell: t -> t*t
val unfold_plus: t -> (t*t)*(t*t)
val prev_unfold_single_cell: t -> t*t
val prev_unfold_plus: t -> (t*t)*(t*t)
val compose_two_cells: t -> t -> int -> int -> int * int -> t
val print_cell: t -> unit
val get_beta_d1:  t -> int
val get_beta_d2:  t -> int
val get_beta_d3:  t -> int*int

val invert_cell_lock: t -> t

val reach_q: t
  
val reach_a: t
val reach_c: t    
  val reach_unordered: t
val reach_hw_q: t
val reach1: t

val reach_multi_set: t

val reach2:t
val reach_equal:t
val data_equal:t
val reach_inv:t
val reach_local:t
val reach_unordered:t  
val emp_beta:beta
val emp_alpha:alpha
val zero_alpha:alpha
val intersect_alpha: t -> t -> alpha
val intersect_beta: t -> t -> beta
val intersect_beta': int -> t -> t -> beta*int*int
val intersect_alpha_beta:int -> t -> t -> int -> int -> (int*int)-> alpha*int*int*(int*int)*int*int*bool
val intersect_beta_alpha: t -> t -> int -> int -> int*int -> alpha*int*int*(int*int)*int
val update_reach_one: t -> t
val reach3:t
val get_alpha_ord: t -> int
val get_beta_ord: t -> int
val assign_color:t -> int -> t