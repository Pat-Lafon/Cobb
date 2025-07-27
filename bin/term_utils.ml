open Term
open Mtyped
open Nt
open Utils
open Cty

let type_to_generator_mapping : (Nt.t * string) list =
  [
    (Ty_int, "int_gen");
    (ty_intlist, "hidden_list_gen");
    (ty_inttree, "hidden_tree_gen");
    (ty_intrbtree, "hidden_rbtree_gen");
    (ty_stlc_term, "hidden_stlc_term_gen");
  ]

let get_ty_gen_name (base_ty : Nt.t) : identifier =
  (List.assoc base_ty type_to_generator_mapping)#:(Ty_arrow (Ty_unit, base_ty))

let term_bot (base_ty : Nt.t) : _ Mtyped.typed = Term.CErr#:base_ty

let term_top (base_ty : Nt.t) : _ Mtyped.typed =
  (*   let ret = (Rename.name ()) #: base_ty in *)
  let unit_value = Constant.U |> constant_to_value in
  (* let unit_name = (Rename.name ()) #: Ty_unit in *)
  let f = get_ty_gen_name base_ty in
  (*  let _, gen_app = Pieces.mk_let_app f unit_name in
  *)
  (*   mk_lete unit_name unit_value gen_app *)
  mk_app (f |> id_to_value) unit_value

let is_base_bot (t : _ Mtyped.typed) : bool =
  match t.x with Term.CErr -> true | _ -> false

(** Keep in Sync with term_top*)
let is_base_top (t : _ Mtyped.typed) : bool =
  match t.x with
  | CLetE
      {
        lhs = _;
        rhs = { x = CVal { x = VVar { x = "TT"; _ }; _ }; _ };
        body = { x = CLetE { body = { x = CVal { x = VVar _; _ }; _ }; _ }; _ };
      } ->
      true
  | CApp { appf = { x = VVar { x; _ }; _ }; _ }
    when List.split type_to_generator_mapping |> snd |> List.mem x ->
      true
  | _ -> false
