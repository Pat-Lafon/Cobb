let rec rbtree_gen (inv : int) (color : bool) (height : int) : int rbtree =
  let (b : bool) = height == 0 in
  if b then
    if color then Rbtleaf
    else
      let (n1 : int) = int_gen () in
      let (lt1 : int rbtree) = Rbtleaf in
      let (rt1 : int rbtree) = Rbtleaf in
      let (res1 : int rbtree) = Rbtnode (true, lt1, n1, rt1) in
      res1
  else if color then
    let (height2 : int) = height - 1 in
    let (lt2 : int rbtree) = rbtree_gen (inv - 1) false height2 in
    let (rt2 : int rbtree) = rbtree_gen (inv - 1) false height2 in
    let (n2 : int) = int_gen () in
    let (res2 : int rbtree) = Rbtnode (false, lt2, n2, rt2) in
    res2
  else
    let (c : bool) = bool_gen () in
    if c then
      let (lt3 : int rbtree) = rbtree_gen (inv - 1) true height in
      let (rt3 : int rbtree) = rbtree_gen (inv - 1) true height in
      let (n3 : int) = int_gen () in
      let (res3 : int rbtree) = Rbtnode (true, lt3, n3, rt3) in
      res3
    else
      let (height4 : int) = height - 1 in
      let (lt4 : int rbtree) = rbtree_gen (inv - 2) false height4 in
      let (rt4 : int rbtree) = rbtree_gen (inv - 2) false height4 in
      let (n4 : int) = int_gen () in
      let (res4 : int rbtree) = Rbtnode (false, lt4, n4, rt4) in
      res4

let[@assert] rbtree_gen =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let c = (true : [%v: bool]) [@over] in
  let[@assert] height =
    (v >= 0 && implies c (v + v == inv) && implies (not c) (v + v + 1 == inv)
      : [%v: int])
      [@over]
  in
  (* the height is the number of black nodes *)
  (numblack v height && noredred v
   && fun (u : int) ->
   (* parent is red; the hdcolor cannot be red *)
   (c && not (hdcolor v true))
   || (* parent is black; the hdcolor can be any color *)
   ((not c) && implies (height == 0) (hdcolor v true))
    : [%v: int rbtree])
    [@under]
