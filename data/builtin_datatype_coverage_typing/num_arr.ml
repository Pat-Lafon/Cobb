let[@library] cons =
  let _ = (true : [%v: stlc_ty]) [@under] in
  let s = (v >= 0 : [%v: int]) [@over] in
  let _ = (size v s : [%v: int list]) [@under] in
  (fun (u : [%forall: int]) -> implies (size v u) (u == s + 1)
    : [%v: int list])
    [@under]
