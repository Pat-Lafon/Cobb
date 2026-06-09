open Zutils
open Language
open Utils
open Tracking
open Context

type t = Nt.t

type block_record = {
  id : identifier;
  ty : Nt.t rty;
  lc : LocalCtx.t;
  cost : int;
}

let rec typed_term_replace_block_body (t : (_, _ term) typed) replacement_body :
    (_, _ term) typed =
  match t.x with
  | CVal _ -> replacement_body
  | CLetE { lhs; rhs; body } ->
      let new_body = typed_term_replace_block_body body replacement_body in
      (CLetE { lhs; rhs; body = new_body })#:new_body.ty
  | CMatch _ | CApp _ | CAppOp _ | CErr ->
      failwith "Unsupported use of typed_term_replace_block_body"
  | CLetDeTuple _ ->
      failwith "typed_term_replace_block_body::CLetDeTuple::unreachable"
  | CRecord _ | CField _ -> failwith "record not supported"

module Pieces = struct
  let mk_let_app_const ~(record : bool) (f : identifier)
      (arg : constant) : identifier * (Nt.t, Nt.t term) typed =
    let ret : identifier = (Rename.fresh_var ())#:(snd @@ Nt.destruct_arr_tp f.ty) in
    let app = mk_app (f |> id_to_value) (arg |> constant_to_value) in
    if record then NameTracking.add_ast ret app else ();
    (ret, mk_lete ret app (ret |> id_to_term))

  let mk_let_app ~(record : bool) (f : identifier) (arg : identifier) :
      identifier * (Nt.t, Nt.t term) typed =
    assert (not (Nt.is_base_tp f.ty));
    let new_ret_ty =
      Nt.destruct_arr_tp f.ty |> fun (l, t) -> Nt.construct_arr_tp (List.tl l, t)
    in
    let ret : identifier = (Rename.fresh_var ())#:new_ret_ty in
    let app = mk_app (f |> id_to_value) (arg |> id_to_value) in
    if record then NameTracking.add_ast ret app else ();
    (ret, mk_lete ret app (ret |> id_to_term))

  let mk_let_appops ~(record : bool) (f : (Nt.t, op) typed)
      (args : identifier list) : identifier * (Nt.t, Nt.t term) typed =
    let ret : identifier = (Rename.fresh_var ())#:(snd @@ Nt.destruct_arr_tp f.ty) in
    let app = mk_appop f (List.map id_to_value args) in
    if record then NameTracking.add_ast ret app else ();
    (ret, mk_lete ret app (ret |> id_to_term))

  let mk_let ~(record : bool) (f : identifier) =
    let ret = (Rename.fresh_var ())#:f.ty in
    let rhs = f |> id_to_term in
    if record then NameTracking.add_ast ret rhs else ();
    (ret, mk_lete ret rhs (ret |> id_to_term))

  let mk_ND_choice (t1 : ('a, 'a term) typed) (t2 : ('a, 'a term) typed) =
    assert (t1.ty = t2.ty);
    let f = "bool_gen"#:(Nt.Ty_arrow (Nt.unit_ty, Nt.bool_ty)) in
    let ret = (Rename.fresh_var ())#:(snd @@ Nt.destruct_arr_tp f.ty) in
    let arg = U |> constant_to_value in
    let app = mk_app (f |> id_to_value) arg in
    NameTracking.add_ast ret app;
    let body =
      (CMatch
         {
           matched = ret |> id_to_value;
           match_cases =
             [
               CMatchcase
                 { constructor = "True"#:Nt.bool_ty; args = []; exp = t1 };
               CMatchcase
                 { constructor = "False"#:Nt.bool_ty; args = []; exp = t2 };
             ];
         })#:t1.ty
    in
    mk_lete ret app body

  type component = Fun of identifier | Op of (Nt.t, op) typed

  let component_cost c =
    match c with
    (* Component is the recursive call*)
    | Fun f
      when Option.fold ~none:false
             ~some:(fun (n, _, _) -> String.equal n f.x)
             (Typing.Common.get_cur_rec_func_name ()) ->
        1
        (* Component produces a type of the same type as a recursive call(goal
           type) *)
    | Fun f
      when Option.fold ~none:false
             ~some:(fun (_, _, ty) -> Nt.equal_nt (Nt.destruct_arr_tp f.ty |> snd) ty)
             (Typing.Common.get_cur_rec_func_name ()) ->
        10
    | Fun _ -> 15
    | Op f
      when Option.fold ~none:false
             ~some:(fun (_, _, ty) -> Nt.equal_nt (Nt.destruct_arr_tp f.ty |> snd) ty)
             (Typing.Common.get_cur_rec_func_name ()) ->
        10
    | Op _ -> 15

  (** The cost of function arguments *)
  let arg_cost : int = 1

  (** The cost of a simple generator like `bool_gen ()` *)
  let base_gen_cost : int = 1

  (** The cost of a 0-arity seed *)
  let seed_cost s_ty =
    Option.fold ~none:5
      ~some:(fun (_, _, ty) ->
        if Nt.equal_nt s_ty ty then 10 else if Nt.equal_nt s_ty Nt.bool_ty then 1 else 5)
      (Typing.Common.get_cur_rec_func_name ())

  let layout_component (c : component) : string =
    match c with Fun f -> f.x | Op op -> op_name_for_typectx op.x

  let string_to_component (s : identifier) : component =
    if is_builtin_op s.x then Op (PrimOp s.x)#:s.ty
    else if is_dt_op s.x then Op (DtConstructor s.x)#:s.ty
    else Fun s

  let mk_app (f_id : identifier) (args : identifier list) _ :
      identifier * (t, t term) typed =
    assert (List.length args >= 1);
    let res =
      List.fold_left
        (fun ((resid : _ typed), aterm) arg ->
          assert (not (Nt.is_base_tp resid.ty));
          let id, new_app = mk_let_app ~record:true resid arg in
          let x = typed_term_replace_block_body aterm new_app in
          (id, x))
        (f_id, f_id |> id_to_term)
        args
    in
    res

  let mk_op (ctor : (Nt.t, op) typed) (args : identifier list) _ :
      identifier * (t, t term) typed =
    let aterm = mk_let_appops ~record:true ctor args in
    aterm

  let apply (comp : component) (args : identifier list) : identifier * _ typed =
    let resid, aterm =
      match comp with
      | Fun f -> mk_app f args id_to_term
      | Op op -> mk_op op args id_to_term
    in
    (*  let () = Hashtbl.add asts resid term in *)
    (resid, aterm)

  let ut_subst (ut : t rty) (ht : (string, identifier) Hashtbl.t) : t rty =
    let renamed_ty =
      List.fold_left
        (fun t { x = name; ty } ->
          if NameTracking.is_known name#:ty then t
          else
            let new_name =
              match Hashtbl.find_opt ht name with
              | Some s -> s
              | None ->
                  print_endline "ut_subst::failed to find mapping:";
                  Hashtbl.iter (fun k v -> k ^ " -> " ^ v.x |> print_endline) ht;
                  failwith ("ut_subst::failed to find " ^ name ^ " in mapping")
            in
            assert (new_name.ty = ty);
            subst_rty_instance name (AVar new_name) t)
        ut (fv_rty ut)
    in
    renamed_ty

  type new_seed = block_record

  let selfification (x : string) (nt : Nt.t) =
    let new_name = (Rename.fresh_var ())#:nt in
    NameTracking.known_ast new_name (id_to_term (NameTracking.known_var x#:nt));
    let new_rty_type =
      RtyBase
        {
          ou = Under;
          cty =
            {
              nty = nt;
              phi =
                Lit
                  (AAppOp
                     ( "=="#:(Nt.Ty_arrow (nt, Nt.Ty_arrow (nt, Nt.bool_ty))),
                       [ (AVar "v"#:nt)#:nt; (AVar x#:nt)#:nt ] ))#:Nt.bool_ty;
            };
        }
    in
    let new_seed : new_seed =
      {
        id = new_name;
        ty = new_rty_type;
        lc = Typectx.ctx_from_list [ new_name.x#:new_rty_type ];
        cost = arg_cost;
      }
    in

    new_seed

  let seeds_from_args (ctx : Nt.t rty Typectx.ctx) : new_seed list =
    List.filter_map
      (fun { x; ty } ->
        match ty with
        | RtyBase _ ->
            let nty = erase_rty ty in
            let new_seed = selfification x nty in
            Some new_seed
        | _ -> None)
      (Typectx.ctx_to_list ctx)

  let components_from_args (ctx : Nt.t rty Typectx.ctx) :
      (component * (t list * t)) list =
    List.filter_map
      (fun { x; ty } ->
        let nt = erase_rty ty in
        match ty with
        | RtyBase _ -> None
        | RtyArr
            { argrty = RtyBase { cty = { nty = Nt.Ty_constructor ("unit", []); _ }; _ }; retty = RtyBase _; _ } ->
            failwith "components_from_args::RtyBaseArr::unreachable"
        | RtyArr _ ->
            let id = x#:nt |> NameTracking.known_var in
            let new_component : component * (t list * t) =
              (string_to_component id, nt |> Nt.destruct_arr_tp)
            in
            Some new_component
        | _ -> failwith "components_from_args::Other::unreachable")
      (Typectx.ctx_to_list ctx)

  let seeds_and_components (ctx : Nt.t rty Typectx.ctx)
      (component_list : string list) :
      new_seed list * (component * (t list * t)) list =
    List.fold_left
      (fun (seeds, components) { x; ty } ->
        if not (List.mem x component_list) then (seeds, components)
        else
          let nt = erase_rty ty in
          match ty with
          | RtyBase _ ->
              NameTracking.known_ast x#:nt
                (mk_appop (DtConstructor x)#:nt []);
              let name, _ = mk_let ~record:false x#:nt in
              NameTracking.known_ast name (x#:nt |> id_to_term);
              (* ?? *)
              let new_seed : new_seed =
                {
                  id = name;
                  ty;
                  lc = Typectx.ctx_from_list [ name.x#:ty ];
                  cost = seed_cost nt;
                }
              in
              (new_seed :: seeds, components)
          | RtyArr
              {
                argrty = RtyBase { cty = { nty = Nt.Ty_constructor ("unit", []); phi }; _ };
                retty = RtyBase _ as retty;
                _;
              } ->
              assert (
                phi = Lit { x = AC (B true); ty = Nt.bool_ty });
              let nt_ty = erase_rty retty in
              let name, _ = mk_let_app_const ~record:true x#:nt U in
              let new_seed : new_seed =
                {
                  id = name;
                  ty = retty;
                  lc = Typectx.ctx_from_list [ name.x#:retty ];
                  cost = base_gen_cost;
                }
              in

              (new_seed :: seeds, components)
          | RtyArr _ ->
              let new_component : component * (t list * t) =
                ( string_to_component (x#:nt |> NameTracking.known_var),
                  nt |> Nt.destruct_arr_tp )
              in
              (seeds, new_component :: components)
          | RtyPolyType _ | RtyPolyPred _ ->
              failwith "seeds_and_components::polymorphic rty not supported")
      ([], []) (Typectx.ctx_to_list ctx)
end
