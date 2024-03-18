(* The datatype constructor should use the lower case instead of the first char
*)

type unit = TT
type bool = True | False
type 'a list = Nil | Cons of 'a * 'a list
type 'a pairinghp = Phpleaf | Phpnode of 'a * 'a pairinghp list
type 'a tree = Leaf | Node of 'a * 'a tree * 'a tree
type 'a heap = Hempty | Hnode of 'a * 'a heap * 'a heap
type 'a set = Sempty | Snode of 'a * 'a set * 'a set
type 'a binomialhp = Bhpleaf | Bhpnode of int * 'a * 'a binomialhp list
type 'a rbtree = Rbtleaf | Rbtnode of bool * 'a rbtree * 'a * 'a rbtree
type 'a skewhp = Shpnode of int * 'a * 'a list * 'a skewhp list
type 'a splayhp = Sphpleaf | Sphpnode of 'a splayhp * 'a * 'a splayhp
type 'a unbset = Usleaf | Usnode of 'a * 'a unbset * 'a unbset
type 'a batchedq = Batchedq of 'a list * 'a list
type 'a lazyty = Lazyty of 'a
type 'a stream = Streamnil | Streamlazycons of 'a * 'a stream lazyty
type 'a bankersq = Bankersq of int * 'a stream * int * 'a stream
type 'a ulist = Unil | Ucons of 'a * 'a ulist
type 'a ctree = Cleaf | Cnode of 'a * 'a ctree * 'a ctree

type 'a leftisthp =
  | Lhpleaf
  | Lhpnode of 'a * 'a leftisthp * 'a leftisthp * int

type stlc_ty = Stlc_ty_nat | Stlc_ty_arr of stlc_ty * stlc_ty

type stlc_term =
  | Stlc_const of int
  | Stlc_id of int
  | Stlc_app of stlc_term * stlc_term
  | Stlc_abs of stlc_ty * stlc_term

type stlc_tyctx = Stlc_tyctx_nil | Stlc_tyctx_cons of stlc_ty * stlc_tyctx
