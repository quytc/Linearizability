
(* type t = (Data.t * Data.t) array *)
(* let get_value s v = assert(Label.is_local v); fst s.(Label.unpack v) *)
(* let set_value s v d = assert(Label.is_local v); s.(Label.unpack v) <- d, snd s.(Label.unpack v) *)
(* let get_org_value s v = assert(Label.is_local v); snd s.(Label.unpack v) *)
(* let set_org_value s v d = assert(Label.is_local v); s.(Label.unpack v) <- d,d *)
(* let create size = Array.make size (Data.bottom,Data.bottom) *)
(* let clone = Array.copy *)
