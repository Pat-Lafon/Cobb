let[@library] stlc_id =
  let c = (v >= 0 : [%v: int]) [@over] in
  (is_id_eq v c : [%v: stlc_term]) [@under]
