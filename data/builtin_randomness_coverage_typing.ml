(* the built-in random generators *)

(*
let[@library] int_range =
  let a = (true : [%v: int]) [@over] in
  let b = (1 + a < v : [%v: int]) [@over] in
  (a < v && v < b : [%v: int]) [@under]
*)

let[@library] bool_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: bool]) [@under]

let[@library] int_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int]) [@under]

let[@library] hidden_list_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int list]) [@under]

(*
let[@library] nat_gen =
  let _ = (true : [%v: unit]) [@over] in
  (v >= 0 : [%v: int]) [@under]

let[@library] int_range_inc =
  let a = (true : [%v: int]) [@over] in
  let b = (a <= v : [%v: int]) [@over] in
  (a <= v && v <= b : [%v: int]) [@under]

let[@library] int_range_inex =
  let a = (true : [%v: int]) [@over] in
  let b = (a <= v : [%v: int]) [@over] in
  (a <= v && v < b : [%v: int]) [@under]

let[@library] increment =
  let n = (true : [%v: int]) [@over] in
  (v == n + 1 : [%v: int]) [@under]
*)
let[@library] decrement =
  let n = (true : [%v: int]) [@over] in
  (v == n - 1 : [%v: int]) [@under]

let[@library] lt_eq_one =
  let s = (true : [%v: int]) [@over] in
  (iff v (s <= 1) && iff (not v) (s > 1) : [%v: bool]) [@under]
(*
(* uniquel  *)

let[@library] gt_eq_int_gen =
  let x = (true : [%v: int]) [@over] in
  (true : [%v: int]) [@under]
*)

let[@library] sizecheck =
  let x = (true : [%v: int]) [@over] in
  (iff v (x == 0) && iff (not v) (x > 0) : [%v: bool]) [@under]

let[@library] subs =
  let s = (true : [%v: int]) [@over] in
  (v == s - 1 : [%v: int]) [@under]
