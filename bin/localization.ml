open Term
open Mtyped
open Nt
open Rty
open Typing.Termcheck
open Language.FrontendTyped
open Subtyping.Subrty
open Utils
open Cty

type 'a exn_variations = { full_exn : 'a; other : 'a list }

let type_to_generator_mapping : (Nt.t * string) list =
  [
    (Ty_int, "int_gen");
    (ty_intlist, "hidden_list_gen");
    (ty_inttree, "hidden_tree_gen");
    (ty_intrbtree, "hidden_rbtree_gen");
  ]

let term_bot base_ty : _ Mtyped.typed = Term.CErr #: base_ty

let term_top (base_ty : Nt.t) : _ Mtyped.typed =
  (*   let ret = (Rename.name ()) #: base_ty in *)
  let unit_value = Constant.U |> constant_to_value in
  (* let unit_name = (Rename.name ()) #: Ty_unit in *)
  let f =
    (List.assoc base_ty type_to_generator_mapping)
    #: (Ty_arrow (Ty_unit, base_ty))
  in
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

let not_map_base f t = if is_base_bot t || is_base_top t then t else f t

let exn_map (f : _ -> _) (v : _ exn_variations) : _ exn_variations =
  assert (v.other != []);
  {
    full_exn = not_map_base f v.full_exn;
    other = List.map (not_map_base f) v.other;
  }

let exn_map_list (f : 'a list -> 'b) (v : 'a exn_variations list) :
    'b exn_variations =
  let exn_list = List.map (fun x -> x.full_exn) v in
  let other =
    List.mapi
      (fun idx x -> List.map (fun y -> f (replace exn_list idx y)) x.other)
      v
    |> List.concat
  in
  { full_exn = f exn_list; other }

let rec term_exnify body : _ exn_variations =
  match body.x with
  | CErr -> { full_exn = term_bot body.ty; other = [ term_top body.ty ] }
  | CVal { ty; _ } ->
      assert (body.ty = ty);
      { full_exn = term_bot ty; other = [ term_top ty ] }
  | CApp _ -> failwith ("unimplemented CApp: " ^ layout_typed_term body)
  | CAppOp _ -> { full_exn = term_bot body.ty; other = [ term_top body.ty ] }
  | CLetE { lhs; rhs; body } ->
      term_exnify body
      |> exn_map (fun x -> { x = CLetE { lhs; rhs; body = x }; ty = body.ty })
  | CLetDeTu { turhs; tulhs; body } ->
      term_exnify body
      |> exn_map (fun x ->
             { x = CLetDeTu { turhs; tulhs; body = x }; ty = body.ty })
  | CMatch { matched; match_cases } ->
      let exn_cases = List.map case_exnify match_cases in
      exn_map_list
        (fun l ->
          assert (List.length l == List.length match_cases);
          { x = CMatch { matched; match_cases = l }; ty = body.ty })
        exn_cases

and case_exnify (CMatchcase { constructor; args; exp } : _ match_case) :
    _ match_case exn_variations =
  let { full_exn; other } = term_exnify exp in
  let f x = CMatchcase { constructor; args; exp = x } in
  { full_exn = f full_exn; other = List.map f other }

module Localization = struct
  let add_props_to_base (base : _ rty) (props : _ Prop.prop list) : _ rty =
    match base with
    | RtyBase { ou; cty = Cty { nty; phi } } ->
        RtyBase { ou; cty = Cty { nty; phi = smart_and (phi :: props) } }
    | _ -> failwith "unimplemented"

  let localization (uctx : uctx) (body : (Nt.t, Nt.t Term.term) Mtyped.typed)
      (target_ty : Nt.t rty) : _ list =
    print_endline "LOCALIZATION";

    pprint_simple_typectx_judge uctx (layout_typed_term body, target_ty);

    print_endline (layout_rty target_ty);
    print_endline ("BODY: " ^ layout_typed_term body);
    let inferred_body = term_type_infer uctx body |> Option.get in
    pprint_simple_typectx_judge uctx
      ( inferred_body |> map_typed_term erase_rty |> layout_typed_term,
        inferred_body.ty );

    print_endline ("Inferred whole type" ^ layout_rty inferred_body.ty);

    let exnified = term_exnify body in

    let program_variations = exnified.other in

    (* program_variations |> List.iter (fun x -> print_endline (NL.layout x));
       (); *)
    let inferred_program_types =
      List.map (term_type_infer uctx) program_variations
      |> List.map Option.get
      |> List.combine program_variations
    in

    print_endline "\nInferred path conditions";

    inferred_program_types
    |> List.iter (fun (x, y) ->
           pprint_typectx_infer uctx.local_ctx (layout_typed_term x, y.ty));
    ();

    print_string "\nInitial subtyping check: ";
    sub_rty_bool uctx (target_ty, target_ty) |> string_of_bool |> print_endline;

    let possible_props =
      List.split inferred_program_types
      |> snd
      |> List.map (fun x -> x.ty |> assume_base_rty |> snd)
      |> List.map (fun (Cty { phi; _ }) -> Prop.Not phi)
    in

    (* Check that on it's own, the inferred type is no sufficient *)
    assert (not (sub_rty_bool uctx (inferred_body.ty, target_ty)));

    ((* Check that with all path conditions negated, the inferred type is trivially sufficient but not vaciously so *)
     let modified_target_ty = add_props_to_base target_ty possible_props in
     assert (sub_rty_bool uctx (inferred_body.ty, modified_target_ty));
     assert (not (sub_rty_bool uctx (modified_target_ty, inferred_body.ty))));

    let useful_props =
      List.fold_left
        (fun acc idx ->
          let ps = Core.List.drop possible_props idx in
          let current_prop = List.hd ps in
          let rest_props = List.tl ps in
          Zzdatatype.Datatype.List.split_by_comma layout_prop ps
          |> print_endline;

          (* Does the check work without this prop?*)
          let modified_target_ty =
            add_props_to_base target_ty (List.concat [ acc; rest_props ])
          in
          (* TODO: Not worried about timeout here I think? *)
          let subtyping_res =
            sub_rty_bool uctx (inferred_body.ty, modified_target_ty)
          in

          subtyping_res |> string_of_bool |> print_endline;
          if subtyping_res then acc else current_prop :: acc)
        []
        (range (List.length possible_props))
    in

    (* Zzdatatype.Datatype.List.split_by_comma layout_prop useful_props
       |> print_endline;
    *)
    let remove_negations_in_props =
      List.map
        (fun x ->
          match x with Prop.Not p -> p | _ -> failwith (layout_prop x))
        useful_props
    in

    print_string "\nUseful path props: ";
    Zzdatatype.Datatype.List.split_by_comma layout_prop
      remove_negations_in_props
    |> print_endline;

    remove_negations_in_props
end

let%test "bot_int" =
  let ty = Ty_int in
  let t = term_bot ty in
  is_base_bot t

let%test "bot_list" =
  let ty = Ty_constructor ("list", [ Ty_int ]) in
  let t = term_bot ty in
  is_base_bot t

let%test "top_int" =
  let ty = Ty_int in
  let t = term_top ty in
  is_base_top t

let%test "top_list" =
  let ty = Ty_constructor ("list", [ Ty_int ]) in
  let t = term_top ty in
  is_base_top t
