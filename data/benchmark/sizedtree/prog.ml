let rec sized_tree_gen (size : int) : int tree =
  let (b : bool) = size == 0 in
  if b then Leaf
  else
    let (b1 : bool) = bool_gen () in
    if b1 then Leaf
    else
      let (size1 : int) = size - 1 in
      let (lt : int tree) = sized_tree_gen size1 in
      let (rt : int tree) = sized_tree_gen size1 in
      let (n : int) = int_gen () in
      Node (n, lt, rt)

let[@assert] sized_tree_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun (u : int) -> implies (depth v u) (0 <= u && u <= s)
    : [%v: int tree])
    [@under]
