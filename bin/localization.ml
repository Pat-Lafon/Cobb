open Term
open Mtyped
open Nt
open Rty
open Typing.Termcheck
open Language.FrontendTyped
open Subtyping.Subrty
open Utils
open Cty
open Block
open Blocks
open Tracking
open Pieces
open Context

type 'a exn_variations = {
  full_exn : 'a;
  hole_variation : 'a;
  other : ('a * (t rty, string) typed list * string) list;
}

let type_to_generator_mapping : (Nt.t * string) list =
  [
    (Ty_int, "int_gen");
    (ty_intlist, "hidden_list_gen");
    (ty_inttree, "hidden_tree_gen");
    (ty_intrbtree, "hidden_rbtree_gen");
  ]

let term_bot (base_ty : Nt.t) : _ Mtyped.typed = Term.CErr #: base_ty

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

let not_map_base_triple f (t, b, c) =
  if is_base_bot t || is_base_top t then (t, [], c) else (f t, b, c)

(** if the thing is not top/bot, then apply f and add local_vars, else return
  top/bot and no vars *)
let exn_map (f : _ -> _) (local_vars : _ list) (v : _ exn_variations) :
    _ exn_variations =
  assert (v.other != []);
  {
    full_exn = not_map_base f v.full_exn;
    hole_variation = f v.hole_variation;
    other =
      List.map (fun (a, b, d) -> (a, local_vars @ b, d)) v.other
      |> List.map (not_map_base_triple f);
  }

(** Applies multiple exn_variations as a arguments to f *)
let exn_map_list_term (f : 'a list -> 'b) (v : 'a exn_variations list) :
    'b exn_variations =
  let exn_list, hole_list =
    List.map
      (fun x ->
        ( x.full_exn,
          if is_base_bot x.full_exn then
            let () = assert (List.length x.other == 1) in
            let _, _, _c = List.hd x.other in
            x.hole_variation
            (* Pieces.mk_ND_choice x.hole_variation
               (c #: x.hole_variation.ty |> id_to_term) *)
          else x.hole_variation ))
      v
    |> List.split
  in
  let other =
    List.mapi
      (fun idx x ->
        List.map
          (fun (y, vars, s) -> (f (replace exn_list idx y), vars, s))
          x.other)
      v
    |> List.concat
  in
  { full_exn = f exn_list; hole_variation = f hole_list; other }

(** Applies multiple exn_variations as a arguments to f *)
let exn_map_list_match (f : 'a Term.match_case list -> 'b)
    (v : 'a Term.match_case exn_variations list) : 'b exn_variations =
  let exn_list, hole_list =
    List.map
      (fun x ->
        ( x.full_exn,
          let is_bot =
            let (CMatchcase { constructor; args; exp }) = x.full_exn in
            is_base_bot exp
          in

          match x.hole_variation with
          | CMatchcase { constructor; args; exp } when is_bot ->
              let () = assert (List.length x.other = 1) in
              let _, _, c = List.hd x.other in
              CMatchcase
                {
                  constructor;
                  args;
                  exp = Pieces.mk_ND_choice exp (c #: exp.ty |> id_to_term);
                }
          | CMatchcase { constructor; args; exp } ->
              CMatchcase { constructor; args; exp } ))
      v
    |> List.split
  in
  let other =
    List.mapi
      (fun idx x ->
        List.map
          (fun (y, vars, s) -> (f (replace exn_list idx y), vars, s))
          x.other)
      v
    |> List.concat
  in
  { full_exn = f exn_list; hole_variation = f hole_list; other }

let promote_true_rty (x : (t, string) typed) : (t rty, string) typed =
  x #=> (fun nty ->
  RtyBase
    {
      ou = false;
      cty = Cty { nty; phi = Prop.Lit (Lit.AC (B true)) #: Ty_bool };
    })

let rec term_exnify (body : (t, t term) typed) : (t, _) typed exn_variations =
  match body.x with
  | CErr ->
      {
        full_exn = term_bot body.ty;
        hole_variation = body;
        other = [ (term_top body.ty, [], Rename.unique "Hole") ];
      }
  | CVal { ty; _ } ->
      assert (body.ty = ty);
      {
        full_exn = term_bot body.ty;
        hole_variation = body;
        other = [ (term_top body.ty, [], Rename.unique "Hole") ];
      }
  | CApp _ -> failwith "unimplemented CApp: "
  | CAppOp _ ->
      {
        full_exn = term_bot body.ty;
        hole_variation = body;
        other = [ (term_top body.ty, [], Rename.unique "Hole") ];
      }
  | CLetE { lhs; rhs; body } ->
      term_exnify body
      |> exn_map
           (fun (x : (t, t term) typed) : (t, t term) typed ->
             (CLetE { lhs; rhs; body = x }) #: body.ty)
           [ promote_true_rty lhs ]
  | CLetDeTu { turhs; tulhs; body } ->
      term_exnify body
      |> exn_map
           (fun x -> (CLetDeTu { turhs; tulhs; body = x }) #: body.ty)
           (List.map promote_true_rty tulhs)
  | CMatch { matched; match_cases } ->
      let exn_cases = List.map case_exnify match_cases in
      exn_map_list_match
        (fun l ->
          assert (List.length l = List.length match_cases);
          { x = CMatch { matched; match_cases = l }; ty = body.ty })
        exn_cases

and case_exnify (CMatchcase { constructor; args; exp } : _ match_case) :
    _ match_case exn_variations =
  let { full_exn; hole_variation; other } = term_exnify exp in
  let f x = CMatchcase { constructor; args; exp = x } in
  {
    full_exn = f full_exn;
    hole_variation = f hole_variation;
    other = List.map (fun (a, b, c) -> (f a, b, c)) other;
  }

let mk_path_var (phi : _ Prop.prop) : (t rty, string) typed =
  let path_name = (Rename.unique path_condition_prefix) #: Ty_unit in
  (path_name |> NameTracking.known_var) #=> (fun l ->
  RtyBase { ou = false; cty = Cty { nty = Nt.Ty_unit; phi } })

let remove_local_vars_from_prop (phi : _ Prop.prop) (local_vars : _ list) :
    _ Prop.prop =
  let local_var_names = List.map (fun x -> x.x) local_vars in
  let rec remove_local_vars_from_prop' (phi : _ Prop.prop) : _ Prop.prop =
    match phi with
    | Prop.Lit _ -> phi
    | Prop.Not p -> Prop.Not (remove_local_vars_from_prop' p)
    | Prop.And ps -> Prop.And (List.map remove_local_vars_from_prop' ps)
    | Prop.Or ps -> Prop.Or (List.map remove_local_vars_from_prop' ps)
    | Prop.Implies (p1, p2) ->
        Prop.Implies
          (remove_local_vars_from_prop' p1, remove_local_vars_from_prop' p2)
    | Prop.Iff (p1, p2) ->
        Prop.Iff
          (remove_local_vars_from_prop' p1, remove_local_vars_from_prop' p2)
    | Prop.Forall { qv; body } ->
        if List.mem qv.x local_var_names then remove_local_vars_from_prop' body
        else Prop.Forall { qv; body = remove_local_vars_from_prop' body }
    | Prop.Exists { qv; body } ->
        if List.mem qv.x local_var_names then remove_local_vars_from_prop' body
        else Prop.Exists { qv; body = remove_local_vars_from_prop' body }
    | Prop.Ite (p1, p2, p3) ->
        Prop.Ite
          ( remove_local_vars_from_prop' p1,
            remove_local_vars_from_prop' p2,
            remove_local_vars_from_prop' p3 )
  in
  remove_local_vars_from_prop' phi

module Localization = struct
  let add_props_to_base (base : _ rty) (props : (_ Prop.prop * _ * _) list) :
      _ rty =
    let props = List.map (fun (a, _, _) -> a) props in
    match base with
    | RtyBase { ou; cty = Cty { nty; phi } } ->
        RtyBase { ou; cty = Cty { nty; phi = smart_and (phi :: props) } }
    | _ -> failwith "add_props_to_base::unimplemented"

  let localization (uctx : uctx) (body : (Nt.t, Nt.t Term.term) Mtyped.typed)
      (target_ty : Nt.t rty) :
      (LocalCtx.t * BlockMap.t * string) list
      * (Nt.t, Nt.t Term.term) Mtyped.typed =
    (* print_endline "LOCALIZATION"; *)
    pprint_simple_typectx_judge uctx (layout_typed_term body, target_ty);

    (* print_endline (layout_rty target_ty);
       print_endline ("BODY: " ^ layout_typed_term body); *)
    let inferred_body = term_type_infer uctx body |> Option.get in
    pprint_simple_typectx_judge uctx
      ( inferred_body |> map_typed_term erase_rty |> layout_typed_term,
        inferred_body.ty );

    (* print_endline ("Inferred whole type" ^ layout_rty inferred_body.ty); *)
    let exnified = term_exnify body in

    let new_body = exnified.hole_variation in

    let program_variations = exnified.other in

    (* program_variations |> List.iter (fun x -> print_endline (NL.layout x));
       (); *)
    let inferred_program_types =
      List.map
        (fun (a, b, s) ->
          ( term_type_infer uctx a |> Option.get,
            (* Filter out bool local_vars because those are just variables used in
               conditions and nothing more *)
            List.filter
              (fun x ->
                (not (Rename.has_been_uniqified x.x))
                && erase_rty x.ty <> Ty_bool
                && Nt.is_base_tp (erase_rty x.ty))
              b,
            s ))
        program_variations
      |> List.combine program_variations
    in

    (* print_string "\nInitial subtyping check: "; *)
    (* sub_rty_bool uctx (target_ty, target_ty) |> string_of_bool |> print_endline; *)
    let possible_props =
      List.split inferred_program_types
      |> snd
      |> List.map (fun (x, local_vs, s) ->
             (x.ty |> assume_base_rty |> snd, local_vs, s))
      |> List.map (fun (Cty { phi; _ }, local_vs, s) ->
             (Prop.Not phi, local_vs, s))
    in

    (* print_endline "Possible props: ";
       List.iter
         (fun (x, local_vs, s) ->
           print_endline (layout_prop x);
           List.iter (fun x -> print_endline (layout_id_rty x)) local_vs)
         possible_props; *)

    (* Check that on it's own, the inferred type is not sufficient *)
    assert (not (sub_rty_bool uctx (inferred_body.ty, target_ty)));

    ((* Check that with all path conditions negated, the inferred type is trivially sufficient *)
     let modified_target_ty = add_props_to_base target_ty possible_props in
     assert (sub_rty_bool uctx (inferred_body.ty, modified_target_ty));

     if not (rty_is_false inferred_body.ty) then
       (* but not vaciously so *)
       assert (not (sub_rty_bool uctx (modified_target_ty, inferred_body.ty))));

    (* Lets try and exclude all paths with local variables and see if it still
       checks out
       TODO: If so, we can drop all of those paths... otherwise we need to
       conservatively keep all paths with local variables
       Hypothetically, we could do grouping here but not worth yet. Maybe add
       benchmarks for this *)
    let possible_props =
      let local_free_subset =
        List.filter
          (fun (x, local_vs, s) -> List.is_empty local_vs)
          possible_props
      in

      (* todo, maybe refactor this out since it is used twice *)
      let modified_target_ty = add_props_to_base target_ty local_free_subset in
      (* TODO: Not worried about timeout here I think? *)
      let subtyping_res =
        sub_rty_bool uctx (inferred_body.ty, modified_target_ty)
      in

      if subtyping_res then local_free_subset else possible_props
    in

    (* Path props usually go from more general to more specific(By the nature of
       how trees work) so lets reverse the order to make some cases nicer *)
    let possible_props = List.rev possible_props in

    let useful_props =
      List.fold_left
        (fun acc idx ->
          let ps = Core.List.drop possible_props idx in
          let current_prop = List.hd ps in
          (* Local variables are hard to reason about in terms of which paths
             with local variables are useful.
             So probably just not try to drop them*)
          if current_prop |> (fun (_, b, _) -> b) |> List.is_empty |> not then
            current_prop :: acc
          else
            let rest_props = List.tl ps in

            (* List.map (fun (a, _, _) -> a) ps
               |> Zzdatatype.Datatype.List.split_by_comma layout_prop
               |> print_endline; *)

            (* Does the check work without this prop?*)
            let modified_target_ty =
              add_props_to_base target_ty (List.concat [ acc; rest_props ])
            in
            (* TODO: Not worried about timeout here I think? *)
            let subtyping_res =
              sub_rty_bool uctx (inferred_body.ty, modified_target_ty)
            in

            (* subtyping_res |> string_of_bool |> print_endline; *)
            if subtyping_res then acc else current_prop :: acc)
        []
        (range (List.length possible_props))
    in

    (* Zzdatatype.Datatype.List.split_by_comma layout_prop useful_props
       |> print_endline;
    *)
    let remove_negations_in_props =
      List.map
        (fun (x, local_vs, s) ->
          match x with
          | Prop.Not p -> (p, local_vs, s)
          | _ -> failwith (layout_prop x))
        useful_props
    in

    (* print_string "\nUseful path props and local vars: ";
       remove_negations_in_props
       |> Zzdatatype.Datatype.List.split_by_comma (fun (x, vs, _) ->
              layout_prop x ^ " : "
              ^ Zzdatatype.Datatype.List.split_by_comma layout_id_rty vs)
       |> print_endline; *)
    let res =
      remove_negations_in_props
      |> List.map (fun (x, local_vs, s) ->
             let local_ctx : LocalCtx.t =
               let path_var =
                 mk_path_var (remove_local_vars_from_prop x local_vs)
               in
               (* let _ =
                    NameTracking.known_var path_var.x #: (erase_rty path_var.ty)
                  in *)
               Typectx (local_vs @ [ path_var ])
             in
             let block_map =
               BlockMap.init
                 (List.map
                    (fun local_v ->
                      let nty = erase_rty local_v.ty in
                      let block : Block.t =
                        ( local_v.x #: nty |> NameTracking.known_var,
                          local_v.ty,
                          (* We intentionally want to add the variables before the
                             current local_ctx as we want them available to fill holes
                             from remove_local_vars_from_prop *)
                          local_ctx )
                      in
                      Block.layout block |> print_endline;

                      block)
                    local_vs)
             in
             (local_ctx, block_map, s))
    in
    (res, new_body)
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
