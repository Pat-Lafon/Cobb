let path_condition_prefix = "pathcond"

type identifier = (Nt.t, string) Mtyped.typed

(*** Replace the element at pos of l with a *)
let replace l pos a = List.mapi (fun i x -> if i = pos then a else x) l

(** Creates a version of the list with only unique elements. Secretly reverse
    the order *)
let unique l =
  let rec aux l acc =
    match l with
    | [] -> acc
    | h :: t -> if List.mem h acc then aux t acc else aux t (h :: acc)
  in
  aux l []

let dbg_sexp sexp = print_endline (Core.Sexp.to_string_hum sexp)
let ty_intlist = Nt.Ty_constructor ("list", [ Ty_int ])
let ty_intrbtree = Nt.Ty_constructor ("rbtree", [ Ty_int ])
let ty_inttree = Nt.Ty_constructor ("tree", [ Ty_int ])
let ty_stlc_term = Nt.Ty_constructor ("stlc_term", [])

let rty_is_false (rty : Nt.t Rty.rty) : bool =
  match rty with
  | RtyBase { cty = Cty { phi = Lit { x = AC (B false); _ }; _ }; _ } -> true
  | _ -> false

let map_fst f (l, r) = (f l, r)

(** Produces a list from 0..n-1 *)
let range n = List.init n (fun x -> x)

(** Computes a powerset from a list of elements *
    https://stackoverflow.com/questions/40141955/computing-a-set-of-all-subsets-power-set
*)
let rec superset_helper = function
  | [] -> [ [] ]
  | x :: xs ->
      let ps = superset_helper xs in
      ps @ List.map (fun ss -> x :: ss) ps

(* Superset, except remove the first element which is the nil element *)
let superset l = superset_helper l |> List.tl

(** Takes a list and performs a giant multi-cartesian product * Used to compute
    a new list of function arguments from a list of possible arguments for each
    position *)
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

module Hashtbl = struct
  include Hashtbl

  let is_empty (t : ('a, 'b) t) : bool = length t = 0

  let map (f : 'a * 'b -> 'a * 'c) (t : ('a, 'b) t) : ('a, 'c) t =
    let new_t = create (length t) in
    iter
      (fun k v ->
        let k, v = f (k, v) in
        replace new_t k v)
      t;
    new_t

  let filter_map (f : 'a * 'b -> ('a * 'c) option) (t : ('a, 'b) t) : ('a, 'c) t
      =
    let new_t = create (length t) in
    iter
      (fun k v ->
        match f (k, v) with Some (k, v) -> replace new_t k v | None -> ())
      t;
    new_t
end

module List = struct
  include List

  let is_empty = function [] -> true | _ -> false
end

let _stripe_fun (l : 'b option list) (n : int) (v : 'b option) =
  range n
  |> List.filter_map (fun x ->
         if List.nth l x <> None then None
         else Some (Zzdatatype.Zlist.List.replace_exn l x v))

(* Not the most efficient but it works *)

(** Given an n, make all possible combinations of lists of length n with the
    condition that Some(true) and Some(false) occur atleast once *)
let arg_coloring (n : int) : bool option list list =
  assert (n >= 2);
  let init = List.init n (fun _ -> None) in
  let one = _stripe_fun init n (Some true) in
  let two =
    List.map (fun l -> _stripe_fun l n (Some false)) one |> List.flatten
  in

  if n = 2 then two
  else
    range (n - 2)
    |> List.fold_left
         (fun acc _ ->
           List.map
             (fun l ->
               let l1 = _stripe_fun l n (Some true) in
               let l2 = _stripe_fun l n (Some false) in
               let l3 = _stripe_fun l n None in
               List.flatten [ l1; l2; l3 ])
             acc
           |> List.flatten)
         two
    |> List.sort_uniq compare
