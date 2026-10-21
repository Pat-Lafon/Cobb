type t = {
  synth_bound : int;
  synth_rlimit : int option;
  type_rlimit : int option;
  comp_path : string;
  imprecise : bool;
}

(* Populates the zutils + typechecker + abduction + cobb sections. *)
val bootstrap : Yojson.Safe.t -> unit
val get : unit -> t
