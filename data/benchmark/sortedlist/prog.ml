let rec sorted_list_gen (size : int) (x : int) : int list =
  let (b : bool) = size == 0 in
  if b then []
  else
    let (y : int) = int_gen () in
    if x <= y then
      let (size2 : int) = size - 1 in
      let (l : int list) = sorted_list_gen size2 y in
      let (l2 : int list) = y :: l in
      l2
    else Exn

let[@assert] sorted_list_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (rng v s && fun (u : int) (w : int) ->
   implies (mem v u) (x <= u) && implies (ord v u w) (u <= w)
    : [%v: int list])
    [@under]
