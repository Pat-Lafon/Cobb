let[@library] stlc_const =
  let c = (true : [%v: int]) [@over] in
  (is_const_eq v c : [%v: stlc_term]) [@under]

let[@library] stlc_ty_nat = (size v 0 : [%v: stlc_ty]) [@under]

let[@library] stlc_ty_arr =
  let s1 = (v >= 0 : [%v: int]) [@over] in
  let _ = (size v s1 : [%v: stlc_ty]) [@under] in
  let s2 = (v >= 0 : [%v: int]) [@over] in
  let _ = (size v s2 : [%v: stlc_ty]) [@under] in
  (fun (u : [%forall: int]) -> implies (u == 1 + s1 + s2) (size v u)
    : [%v: stlc_ty])
    [@under]
