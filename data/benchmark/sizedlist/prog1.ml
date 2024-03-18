let rec sized_list_gen (s : int) : int list =
  if s == 0 then Err
  else if bool_gen () then []
  else int_gen () :: sized_list_gen (s - 1)

let[@assert] sized_list_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((n [@exists]) : int) -> len v n && n <= s : [%v: int list]) [@under]
