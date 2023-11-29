let[@library] nil = (rng v 0 : [%v: int list]) [@under]

let[@library] cons =
  let h = (true : [%v: int]) [@over] in
  let s = (true : [%v: int]) [@over] in
  let _ =
    (rng v s && fun (u : [%forall: int]) (w : [%forall: int]) ->
     implies (mem v u) (h <= u) && implies (ord v u w) (u <= w)
      : [%v: int list])
      [@under]
  in
  (fun (u : [%forall: int]) (w : [%forall: int]) ->
     implies (u == s + 1) (rng v u)
     && implies (mem v u) (h <= u)
     && implies (ord v u w) (u <= w)
    : [%v: int list])
    [@under]

let[@library] leaf = (rng v 0 : [%v: int tree]) [@under]

let[@library] node =
  let root = (true : [%v: int]) [@over] in
  let range1 = (v >= 0 : [%v: int]) [@over] in
  let _ =
    (fun (u : [%forall: int]) ->
       implies (mem v u) (root - range1 < u && u < root)
       && sorted v && rng v range1
      : [%v: int tree])
      [@under]
  in
  let ranger = (v >= 0 : [%v: int]) [@over] in
  let _ =
    (fun (u : [%forall: int]) ->
       implies (mem v u) (root < u && u < root + ranger)
       && sorted v && rng v ranger
      : [%v: int tree])
      [@under]
  in
  (fun (u : [%forall: int]) ->
     implies (u == range1 + ranger) (rng v u)
     && implies (mem v u) (root - range1 < u && u < root + ranger)
     && sorted v
    : [%v: int tree])
    [@under]

(* int set *)

let[@library] sempty = (rng v 0 : [%v: int set]) [@under]

let[@library] snode =
  let root = (true : [%v: int]) [@over] in
  let range1 = (v >= 0 : [%v: int]) [@over] in
  let _ =
    (fun (u : [%forall: int]) ->
       implies (mem v u) (root - range1 < u && u < root)
       && sorted v && rng v range1
      : [%v: int set])
      [@under]
  in
  let ranger = (v >= 0 : [%v: int]) [@over] in
  let _ =
    (fun (u : [%forall: int]) ->
       implies (mem v u) (root < u && u < root + ranger)
       && sorted v && rng v ranger
      : [%v: int set])
      [@under]
  in
  (fun (u : [%forall: int]) ->
     implies (u == range1 + ranger) (rng v u)
     && implies (mem v u) (root - range1 < u && u < root + ranger)
     && sorted v
    : [%v: int set])
    [@under]

(* unbset *)

let[@library] usleaf = (rng v 0 : [%v: int unbset]) [@under]

let[@library] usnode =
  let root = (true : [%v: int]) [@over] in
  let range1 = (v >= 0 : [%v: int]) [@over] in
  let _ =
    (fun (u : [%forall: int]) ->
       implies (mem v u) (root - range1 < u && u < root)
       && sorted v && rng v range1
      : [%v: int unbset])
      [@under]
  in
  let ranger = (v >= 0 : [%v: int]) [@over] in
  let _ =
    (fun (u : [%forall: int]) ->
       implies (mem v u) (root < u && u < root + ranger)
       && sorted v && rng v ranger
      : [%v: int unbset])
      [@under]
  in
  (fun (u : [%forall: int]) ->
     implies (u == range1 + ranger) (rng v u)
     && implies (mem v u) (root - range1 < u && u < root + ranger)
     && sorted v
    : [%v: int unbset])
    [@under]
