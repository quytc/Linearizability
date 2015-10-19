module type E =
    sig
      val name: string
      val initial_predicates: Constraint.t list
      val predicate_transformers:  Rule.t list
 end
