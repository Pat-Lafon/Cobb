let rec sized_list_gen (s : int) : int list =
  if s == 0 then [] else if bool_gen () then [] else Err

let[@assert] sized_list_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((n [@exists]) : int) -> len v n && n <= s : [%v: int list]) [@under]
