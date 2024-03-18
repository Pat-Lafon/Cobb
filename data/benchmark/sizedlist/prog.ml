let rec sized_list_gen (size : int) : int list =
  if size == 0 then []
  else if bool_gen () then []
  else int_gen () :: sized_list_gen (size - 1)

let[@assert] sized_list_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((n [@exists]) : int) -> len v n && n <= s : [%v: int list]) [@under]
