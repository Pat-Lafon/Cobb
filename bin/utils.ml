type identifier = (Nt.t, string) Mtyped.typed

(*** Replace the element at pos of l with a *)
let replace l pos a = List.mapi (fun i x -> if i = pos then a else x) l
let dbg_sexp sexp = print_endline (Core.Sexp.to_string_hum sexp)
let ty_intlist = Nt.Ty_constructor ("list", [ Ty_int ])
let ty_intrbtree = Nt.Ty_constructor ("rbtree", [ Ty_int ])
let ty_inttree = Nt.Ty_constructor ("tree", [ Ty_int ])

let rty_is_false (rty : Nt.t Rty.rty) : bool =
  match rty with
  | RtyBase { cty = Cty { phi = Lit { x = AC (B false); _ }; _ }; _ } -> true
  | _ -> false

let map_fst f (l, r) = (f l, r)

(** Produces a list from 0..n-1 *)
let range n = List.init n (fun x -> x)

(** Computes a powerset from a list of elements
  * https://stackoverflow.com/questions/40141955/computing-a-set-of-all-subsets-power-set
    *)
let rec superset_helper = function
  | [] -> [ [] ]
  | x :: xs ->
      let ps = superset_helper xs in
      ps @ List.map (fun ss -> x :: ss) ps

(* Superset, except remove the first element which is the nil element *)
let superset l = superset_helper l |> List.tl

(** Takes a list and performs a giant multi-cartesian product
  * Used to compute a new list of function arguments from a list of possible arguments for each position
*)
let rec n_cartesian_product = function
  | [] -> [ [] ]
  | x :: xs ->
      let rest = n_cartesian_product xs in
      List.concat (List.map (fun i -> List.map (fun rs -> i :: rs) rest) x)

(** Group elements of a list by some property *)
let group_by f lst =
  let rec aux acc f = function
    | [] -> acc
    | h :: t ->
        let new_acc =
          let n = f h in
          match List.assoc_opt n acc with
          | None -> (n, [ h ]) :: acc
          | Some t2 -> (n, h :: t2) :: List.remove_assoc n acc
        in
        aux new_acc f t
  in
  aux [] f lst
