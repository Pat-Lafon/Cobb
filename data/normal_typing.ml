val ( == ) : 'a -> 'a -> bool
val ( != ) : 'a -> 'a -> bool
val ( < ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
(* dt *)

(* val nil : 'a list *)
(* val cons : 'a -> 'a list -> 'a list *)
(* val tt : unit *)
val unil : 'a ulist
val ucons : 'a -> 'a ulist -> 'a ulist

(* others *)
val int_range : int -> int -> int
val bool_gen : unit -> bool
val int_gen : unit -> int
val nat_gen : unit -> int
val hidden_list_gen : unit -> int list
val int_range_inc : int -> int -> int
val int_range_inex : int -> int -> int
val increment : int -> int
val decrement : int -> int
val lt_eq_one : int -> bool
val gt_eq_int_gen : int -> int
val sizecheck : int -> bool
val subs : int -> int
val dummy : unit

(* others *)
val len : 'a list -> int -> bool
val lenF : 'a list -> int
val consF : 'a -> 'a list -> 'a list
val emp : 'a list -> bool
val hd : 'a list -> 'a -> bool
val tl : 'a list -> 'a list -> bool
val list_mem : 'a list -> 'a -> bool
(* val list_min : 'a list -> 'a -> bool *)

(* val ord : 'a list -> 'a -> 'a -> bool *)
val sorted : 'a list -> bool
