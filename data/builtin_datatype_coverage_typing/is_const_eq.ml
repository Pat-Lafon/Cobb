let[@library] stlc_const =
  let c = (true : [%v: int]) [@over] in
  (is_const_eq v c : [%v: stlc_term]) [@under]
