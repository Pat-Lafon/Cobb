open Rty
open Cty
open Language.FrontendTyped
open Utils
open Term
open Mtyped
open Tracking

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
    let ret : identifier =
      (Rename.name ()) #: (snd @@ Nt.destruct_arr_tp f.ty)
    in
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

  let ast_to_string ?(erased = false) (id : identifier) : string =
    let term = NameTracking.get_ast id |> Option.get in
    let tterm = if erased then (* Termlang.erase_type  *) term else term in
    layout_typed_term tterm

  let asts_lookup (a : identifier) =
    let expr = NameTracking.get_ast a in
    Option.value expr ~default:(a |> id_to_term)

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
    assert (List.length args = 1);
    let arg = List.hd args in
    let aterm = mk_let_app ~record:true f_id arg in
    aterm

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
            let new_name = Hashtbl.find ht name in
            Rty.subst_rty_instance name (AVar new_name #: ty) t)
        ut (Rty.fv_rty ut)
    in
    renamed_ty

  type new_seed = (identifier * t rty * t rty Typectx.ctx) * t

  let selfification (x : string) (nt : t) =
    let new_name = (Rename.name ()) #: nt in
    NameTracking.add_ast new_name (id_to_term (NameTracking.known_var x #: nt));
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
            let _ : identifier = NameTracking.known_var x in
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
            failwith "unimplemented"
        | RtyBaseArr _ ->
            let new_component : component * (t list * t) =
              (string_to_component x #: nt, nt |> Nt.destruct_arr_tp)
            in
            Some new_component
        | _ -> failwith "unimplemented")
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
          | RtyArrArr _ -> failwith "unimplemented"
          | RtyTuple _ -> failwith "unimplemented")
      ([], []) ctx_list

  (*
  let mk_if (cond : id NNtyped.typed) (true_branch : id NNtyped.typed)
      (false_branch : id NNtyped.typed) : NL.term =
    let cond = NL.id_to_value cond in
    let e_t = NL.id_to_value true_branch |> NL.value_to_term in
    let e_f = NL.id_to_value false_branch |> NL.value_to_term in
    NL.Ite { cond; e_t; e_f }

  (* A special case for the moment when we want to create if's where the second
     branch is an exception *)
  (* I don't want to bind Exn to an id because then it gets executed after the
     condition no? *)
  let mk_one_sided_if (cond : id NNtyped.typed) (true_branch : id NNtyped.typed)
      : NL.term =
    let cond = NL.id_to_value cond in
    let e_t = NL.id_to_value true_branch |> NL.value_to_term in
    let exn = { x = NL.Exn; ty = true_branch.ty } |> NL.value_to_term in
    NL.Ite { cond; e_t; e_f = exn }

  let mmt_subst_id a before after =
    let aux (t : Underty.MMT.ut_with_copy) before after =
      match t with
      | Underty.MMT.UtNormal t ->
          Underty.MMT.UtNormal (UT.subst_id t before after)
      | Underty.MMT.UtCopy { x; ty } ->
          if String.equal x before then Underty.MMT.UtCopy { x = after; ty }
          else t
    in
    match a with
    | Underty.MMT.Ot t -> Underty.MMT.Ot (ot_subst_id t before after)
    | Underty.MMT.Ut t -> Underty.MMT.Ut (aux t before after)
    | Underty.MMT.Consumed t -> Underty.MMT.Consumed (aux t before after)

  let ut_subst (ut : UT.t) (ht : (id, id) Hashtbl.t) : UT.t =
    let renamed_ty =
      List.fold_left
        (fun t name ->
          let new_name = Hashtbl.find ht name in
          Underty.T.subst_id t name new_name)
        ut (Underty.T.fv ut)
    in
    renamed_ty

  let mmt_subst (mmt : MMT.t) (ht : (id, id) Hashtbl.t) : MMT.t =
    let renamed_ty =
      List.fold_left
        (fun t name ->
          let new_name = Hashtbl.find ht name in
          MMT.mmt_subst_id t name new_name)
        mmt (MMT.fv mmt)
    in
    renamed_ty
 *)
end
