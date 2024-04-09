open Rty
open Cty
open Language.FrontendTyped
open Utils
open Term
open Mtyped
open Tracking

let rec typed_term_replace_block_body (t : (_, _ term) typed) replacement_body :
    (_, _ term) typed =
  match t.x with
  | CVal _ -> replacement_body
  | CLetE { lhs; rhs; body } ->
      let new_body = typed_term_replace_block_body body replacement_body in
      (CLetE { lhs; rhs; body = new_body }) #: new_body.ty
  | CMatch _ | CApp _ | CAppOp _ | CErr ->
      failwith "Unsupported use of typed_term_replace_block_body"
  | CLetDeTu _ ->
      failwith "typed_term_replace_block_body::CLetDeTu::unimplemented"

module Pieces = struct
  let mk_let_app_const ?(record = false) (f : identifier)
      (arg : Constant.constant) : identifier * (Nt.t, Nt.t term) typed =
    let ret : identifier =
      (Rename.name ()) #: (snd @@ Nt.destruct_arr_tp f.ty)
    in
    let app = mk_app (f |> id_to_value) (arg |> constant_to_value) in
    if record then NameTracking.add_ast ret app else ();
    (ret, mk_lete ret app (ret |> id_to_term))

  let mk_let_app ?(record = false) (f : identifier) (arg : identifier) :
      identifier * (Nt.t, Nt.t term) typed =
    assert (not (Nt.is_base_tp f.ty));
    let new_ret_ty =
      Nt.destruct_arr_tp f.ty |> fun (l, t) -> Nt.construct_arr_tp (List.tl l, t)
    in
    let ret : identifier = (Rename.name ()) #: new_ret_ty in
    let app = mk_app (f |> id_to_value) (arg |> id_to_value) in
    if record then NameTracking.add_ast ret app else ();
    (ret, mk_lete ret app (ret |> id_to_term))

  let mk_let_appops ~(record : bool) (f : (t, Op.op) typed)
      (args : identifier list) : identifier * (Nt.t, Nt.t term) typed =
    let ret : identifier =
      (Rename.name ()) #: (snd @@ Nt.destruct_arr_tp f.ty)
    in
    let app = mk_appop f (List.map id_to_value args) in
    if record then NameTracking.add_ast ret app else ();
    (ret, mk_lete ret app (ret |> id_to_term))

  let mk_let ~(record : bool) (f : identifier) =
    let ret = (Rename.name ()) #: f.ty in
    let rhs = f |> id_to_term in
    if record then NameTracking.add_ast ret rhs else ();
    (ret, mk_lete ret rhs (ret |> id_to_term))

  let mk_ND_choice (t1 : ('a, 'a term) typed) (t2 : ('a, 'a term) typed) =
    assert (t1.ty = t2.ty);
    let f = "bool_gen" #: (Nt.Ty_arrow (Nt.Ty_unit, Nt.Ty_bool)) in
    let ret = (Rename.name ()) #: (snd @@ Nt.destruct_arr_tp f.ty) in
    let arg = Constant.U |> constant_to_value in
    let app = mk_app (f |> id_to_value) arg in
    NameTracking.add_ast ret app;
    let body =
      (CMatch
         {
           matched = ret |> id_to_value;
           match_cases =
             [
               CMatchcase
                 { constructor = "True" #: Nt.Ty_bool; args = []; exp = t1 };
               CMatchcase
                 { constructor = "False" #: Nt.Ty_bool; args = []; exp = t2 };
             ];
         })
      #: t1.ty
    in
    mk_lete ret app body

  type component = Fun of identifier | Op of (Nt.t, Op.op) typed

  let layout_component (c : component) : string =
    match c with
    | Fun f -> f.x
    | Op op -> op.x |> Op.sexp_of_op |> Core.Sexp.to_string_hum

  let string_to_component (s : identifier) : component =
    if Op.is_builtin_op s.x then Op (Op.PrimOp s.x) #: s.ty
    else if Op.is_dt_op s.x then Op (Op.DtConstructor s.x) #: s.ty
    else Fun s

  let mk_app (f_id : identifier) (args : identifier list) _ :
      identifier * (t, t term) typed =
    assert (List.length args >= 1);
    let res =
      List.fold_left
        (fun (resid, aterm) arg ->
          assert (not (Nt.is_base_tp resid.ty));
          let id, new_app = mk_let_app ~record:true resid arg in
          let x = typed_term_replace_block_body aterm new_app in
          (id, x))
        (f_id, f_id |> id_to_term)
        args
    in
    res
  (* let arg = List.hd args in
     let aterm = mk_let_app ~record:true f_id arg in
     aterm *)

  let mk_op (ctor : (Nt.t, Op.op) typed) (args : identifier list) _ :
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

  let ut_subst (ut : t rty) (ht : (string, string) Hashtbl.t) : t rty =
    let renamed_ty =
      List.fold_left
        (fun t { x = name; ty } ->
          if NameTracking.is_known name #: ty then t
          else
            let new_name =
              match Hashtbl.find_opt ht name with
              | Some s -> s
              | None ->
                  print_endline "ut_subst::failed to find mapping:";
                  Hashtbl.iter (fun k v -> k ^ " -> " ^ v |> print_endline) ht;
                  failwith ("ut_subst::failed to find " ^ name ^ " in mapping")
            in
            Rty.subst_rty_instance name (AVar new_name #: ty) t)
        ut (Rty.fv_rty ut)
    in
    renamed_ty

  type new_seed = (identifier * t rty * t rty Typectx.ctx) * t

  let selfification (x : string) (nt : t) =
    let new_name = (Rename.name ()) #: nt in
    NameTracking.known_ast new_name
      (id_to_term (NameTracking.known_var x #: nt));
    let new_rty_type =
      Rty.RtyBase
        {
          ou = false;
          cty =
            Cty
              {
                nty = nt;
                phi =
                  Prop.Lit
                    (Lit.AAppOp
                       ( "==" #: (Nt.Ty_arrow (nt, Nt.Ty_arrow (nt, Nt.Ty_bool))),
                         [
                           (Lit.AVar "v" #: nt) #: nt; (Lit.AVar x #: nt) #: nt;
                         ] ))
                    #: Nt.Ty_bool;
              };
        }
    in
    let new_seed : new_seed =
      ((new_name, new_rty_type, Typectx [ new_name.x #: new_rty_type ]), nt)
    in
    new_seed

  let seeds_from_args (Typectx ctx_list : t rty Typectx.ctx) : new_seed list =
    List.filter_map
      (fun { x; ty } ->
        match ty with
        | RtyBase _ ->
            let nty = erase_rty ty in
            let new_seed = selfification x nty in
            let (x, _, _), _ = new_seed in
            Some new_seed
        | _ -> None)
      ctx_list

  let components_from_args (Typectx ctx_list : t rty Typectx.ctx) :
      (component * (t list * t)) list =
    List.filter_map
      (fun { x; ty } ->
        let nt = erase_rty ty in
        match ty with
        | RtyBase _ -> None
        | RtyBaseArr
            { argcty = Cty { nty = Nt.Ty_unit; _ }; retty = RtyBase _; _ } ->
            failwith "components_from_args::RtyBaseArr::unimplemented"
        | RtyBaseArr _ ->
            let id = x #: nt |> NameTracking.known_var in
            let new_component : component * (t list * t) =
              (string_to_component id, nt |> Nt.destruct_arr_tp)
            in
            Some new_component
        | _ -> failwith "components_from_args::Other::unimplemented")
      ctx_list

  let seeds_and_components (Typectx ctx_list : t rty Typectx.ctx) :
      ((identifier * t rty * t rty Typectx.ctx) * t) list
      * (component * (t list * t)) list =
    List.fold_left
      (fun (seeds, components) { x; ty } ->
        if String.starts_with ~prefix:"hidden_" x then (seeds, components)
        else
          let nt = erase_rty ty in
          match ty with
          | RtyBase _ ->
              NameTracking.known_ast x #: nt
                (mk_appop (Op.DtConstructor x) #: nt []);
              let name, _ = mk_let ~record:true x #: nt in
              let new_seed : new_seed =
                ((name, ty, Typectx [ name.x #: ty ]), nt)
              in
              (new_seed :: seeds, components)
          | RtyBaseArr
              {
                argcty = Cty { nty = Nt.Ty_unit; phi };
                retty = RtyBase _ as retty;
                _;
              } ->
              assert (
                phi = Prop.Lit { x = Lit.AC (Constant.B true); ty = Nt.Ty_bool });
              let nt_ty = erase_rty retty in
              let name, _ = mk_let_app_const ~record:true x #: nt Constant.U in
              let new_seed : new_seed =
                ((name, retty, Typectx [ name.x #: retty ]), nt_ty)
              in
              (new_seed :: seeds, components)
          | RtyBaseArr _ ->
              let new_component : component * (t list * t) =
                (string_to_component x #: nt, nt |> Nt.destruct_arr_tp)
              in
              (seeds, new_component :: components)
          | RtyArrArr _ ->
              failwith "seeds_and_components::RtyArrArr::unimplemented"
          | RtyTuple _ ->
              failwith "seeds_and_components::RtyTuple::unimplemented")
      ([], []) ctx_list
end
