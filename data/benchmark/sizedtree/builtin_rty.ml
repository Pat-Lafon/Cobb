let[@library] ( == ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a == b) : [%v: bool]) [@under]

(*
let[@library] neq =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a != b) : [%v: bool]) [@under]

let[@library] lt =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a < b) : [%v: bool]) [@under]

let[@library] gt =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a > b) : [%v: bool]) [@under]

let[@library] le =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a <= b) : [%v: bool]) [@under]

let[@library] ge =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a >= b) : [%v: bool]) [@under]
*)
let[@library] ( + ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (v == a + b : [%v: int]) [@under]

let[@library] ( - ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (v == a - b : [%v: int]) [@under]

let[@library] True = (v : [%v: bool]) [@under]
let[@library] False = (not v : [%v: bool]) [@under]


let[@library] Leaf = (leaf v : [%v: int tree]) [@under]

let[@library] Node =
  let x = (true : [%v: int]) [@over] in
  let lt = (true : [%v: int tree]) [@over] in
  let rt = (true : [%v: int tree]) [@over] in
  (root v x && lch v lt && rch v rt : [%v: int tree]) [@under]

let[@library] bool_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: bool]) [@under]

let[@library] int_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int]) [@under]

let[@library] hidden_tree_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int tree]) [@under]

let[@library] increment =
  let n = (true : [%v: int]) [@over] in
  (v == n + 1 : [%v: int]) [@under]

let[@library] decrement =
  let n = (true : [%v: int]) [@over] in
  (v == n - 1 : [%v: int]) [@under]

let[@library] sizecheck =
  let x = (true : [%v: int]) [@over] in
  (iff v (x == 0) && iff (not v) (x > 0) : [%v: bool]) [@under]

let[@library] subs =
  let s = (true : [%v: int]) [@over] in
  (v == s - 1 : [%v: int]) [@under]
