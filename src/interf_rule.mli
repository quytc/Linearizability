(** Rules are transitions in the system. *)

  type cons = Constraint.t
 
(** A concrete transformer [x := y] *)
  class assign: int -> int -> Label.t -> Label.t -> transformer



(* class data_equality: int -> int -> int -> Label.t -> Label.t -> transformer *)
(* class data_inequality: int -> int -> int -> Label.t -> Label.t -> transformer *)


(** A concrete transformer [x := y.next] *)
    class dot_next_assign: int -> int -> Label.t -> Label.t -> transformer
      class dot_next_assign_dot_next: int -> int -> Label.t -> Label.t -> transformer
  class assign_dot_next: int -> int -> Label.t -> Label.t -> transformer

(** A concrete transformer [x := new_cell()] *)
  class new_cell: int -> int -> ?gc:bool -> Label.t -> transformer

  class next_equality: int -> int -> Label.t -> Label.t -> transformer
	
  class equality: int -> int -> Label.t -> Label.t -> transformer
	class less_than: int -> int -> Label.t -> Label.t -> transformer
	class data_equality_variable: int -> int -> Label.t -> Label.t -> transformer
   class data_assign: int -> int -> Label.t -> int -> transformer
     class data_equality: int -> int -> Label.t -> int -> transformer
       class data_inequality: int -> int -> Label.t -> int -> transformer
	class in_equality: int -> int -> Label.t -> Label.t -> transformer

  class nextReference: int -> int -> Label.t  -> transformer
  class inNextReference: int -> int -> Label.t -> transformer

  class init_thread: int -> int -> Label.t array -> transformer
  class kill_thread: int -> int -> transformer

  class atomic: int -> int -> transformer list -> transformer
  class record_insert: int -> int -> Data.t list -> transformer
 
	class get_marked_assign_dot_next: int -> int -> Label.t -> Label.t -> Label.t -> transformer

    class cas_fail: int -> int -> Label.t -> Label.t -> Label.t -> transformer
	
	class cas_success: int -> int -> Label.t -> Label.t -> Label.t -> transformer
   class attempt_mark: int -> int -> Label.t -> Label.t-> transformer
	   class attempt_mark_fail: int -> int -> Label.t -> Label.t-> transformer
	class cas_success_set: int -> int -> Label.t -> Label.t -> int -> Label.t -> transformer
	class cas_fail_set: int -> int -> Label.t -> Label.t -> int -> Label.t -> transformer