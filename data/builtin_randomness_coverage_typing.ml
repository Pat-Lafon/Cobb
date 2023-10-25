(* the built-in random generators *)

let[@library] int_range =
  let a = (true : [%v: int]) [@over] in
  let b = (1 + a < v : [%v: int]) [@over] in
  (a < v && v < b : [%v: int]) [@under]

let[@library] bool_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: bool]) [@under]

let[@library] int_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int]) [@under]

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
