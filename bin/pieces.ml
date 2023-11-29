open Typecheck
open Underctx
open Languages
open Underty.T
open Normalty.Ast.NT
open Autov.Prop
open Config
open Assertion
open Sugar
open Languages.StrucNA

let dbg_sexp sexp = print_endline (Core.Sexp.to_string_hum sexp)

module Pieces = struct
  let asts : (id, Termlang.term) Hashtbl.t = Hashtbl.create 128

  let ast_to_string ?(erased = false) (id : id) =
    let term = Termlang.make_untyped (Hashtbl.find asts id) in
    let tterm = if erased then Termlang.erase_type term else term in
    Frontend.Expr.layout tterm

  type component =
    | Fun of id NNtyped.typed
    | Op of Op.op
    | Ctor of id NNtyped.typed

  let libseed_or_function (ctx : (id * ty) list) (name : id) (t : UT.t) =
    let nty = UT.erase t in
    let argtys, resty = NT.destruct_arrow_tp nty in
    match argtys with
    | [ Ty_unit ] ->
        let f = Termlang.Var name in
        let unit = Termlang.App ({ ty = None; x = Termlang.Var "tt" }, []) in
        let app =
          Termlang.App ({ ty = None; x = f }, [ { ty = None; x = unit } ])
        in
        let tapp = Termcheck.check ctx { ty = None; x = app } in
        Either.left (tapp.x, snd (Option.get tapp.ty))
    | _ -> Either.right (Fun { x = name; ty = (None, nty) }, (argtys, resty))

  let maybe_op_seed ((op, t) : Op.t * ty) =
    (* Todo substitute further if needed *)
    let concrete = Ty.subst t ("a", Ty_int) in
    match (op, concrete) with
    | _, Ty_unit -> None
    | DtConstructor "nil", Ty_list Ty_int ->
        Some (Either.left (Termlang.Var "nil", concrete))
    | PrimOp op, (Ty_arrow _ as concrete) ->
        Some (Either.right (Op op, NT.destruct_arrow_tp concrete))
    | DtConstructor name, (Ty_arrow _ as concrete) ->
        Some
          (Either.right
             ( Ctor { x = name; ty = (None, concrete) },
               NT.destruct_arrow_tp concrete ))
    | _ ->
        failwith
          (Printf.sprintf "Unknown operation `%s` of type `%s`"
             (Core.Sexp.to_string_hum (Op.sexp_of_t op))
             (Core.Sexp.to_string (Ty.sexp_of_t concrete)))

  (* NOTE: the code below shows what operations are available according
     to where the type checker looks *)
  let ops () = Abstraction.Prim_map.get_normal_m ()

  let prim_gathering_helper () =
    List.partition_map
      (fun a -> a)
      (List.filter_map maybe_op_seed
         (Abstraction.Prim_map.S.fold
            (fun op arg tail -> (op, arg) :: tail)
            (ops ()) []))

  let library_gathering_helper (libs : (id * UT.t) list) =
    List.partition_map
      (fun (name, uty) ->
        libseed_or_function
          (List.map (fun (n, t) -> (n, UT.erase t)) libs)
          name uty)
      libs

  let builtin_seeds =
    [
      (Termlang.Const (Termcheck.V.B false), Ty_bool);
      (Termlang.Const (Termcheck.V.B true), Ty_bool);
      (Termlang.Const (Termcheck.V.I 0), Ty_int);
      (Termlang.Const (Termcheck.V.I 1), Ty_int);
    ]

  let mk_seed (x, y) =
    let name = Rename.name () in
    Hashtbl.add asts name x;
    ((name, Trans.to_anormal_with_name name false { x; ty = Some (None, y) }), y)

  let seeds_and_components (libs : (id * UT.t) list) =
    (* I move this inside of a function becuase `Abstraction.Prim_map.get_normal_m` will call some global reference that hasn't been set yet *)
    (* Main sets this ref, but this file gets built first *)
    let prim_seeds, operations = prim_gathering_helper () in
    let lib_seeds, funs = library_gathering_helper libs in
    let seeds = prim_seeds @ lib_seeds @ builtin_seeds in
    (List.map mk_seed seeds, operations @ funs)

  let known : (id, unit) Hashtbl.t = Hashtbl.create 128

  let known_var (a : id) =
    Hashtbl.add known a ();
    Hashtbl.add asts a (Termlang.Var a);
    a

  let asts_lookup (a : id NNtyped.typed) =
    let expr = Option.map Termlang.make_untyped (Hashtbl.find_opt asts a.x) in
    Option.value expr ~default:(Termlang.make_untyped (Termlang.Var a.x))

  let mk_app (f_id : id NNtyped.typed) (args : id NNtyped.typed list) k :
      id NNtyped.typed * NL.term * Termlang.term =
    let name = Rename.name () in
    let resty = snd (NT.destruct_arrow_tp (snd f_id.ty)) in
    let resid : id NNtyped.typed = { x = name; ty = (None, resty) } in
    let term =
      Termlang.App
        (Termlang.make_untyped (Termlang.Var f_id.x), List.map asts_lookup args)
    in
    let args = List.map NL.id_to_value args in
    let aterm = NL.LetApp { ret = resid; f = f_id; args; body = k resid } in
    (resid, aterm, term)

  let mk_ctor (ctor : id NNtyped.typed) (args : id NNtyped.typed list) k :
      id NNtyped.typed * NL.term * Termlang.term =
    let name = Rename.name () in
    let resty = snd (NT.destruct_arrow_tp (snd ctor.ty)) in
    let resid : id NNtyped.typed = { x = name; ty = (None, resty) } in
    let term =
      Termlang.App
        (Termlang.make_untyped (Termlang.Var ctor.x), List.map asts_lookup args)
    in
    let args = List.map NL.id_to_value args in
    let aterm =
      NL.LetDtConstructor { ret = resid; f = ctor; args; body = k resid }
    in
    (resid, aterm, term)

  let mk_op (op_id : Op.op) (args : id NNtyped.typed list) :
      id NNtyped.typed * NL.term * Termlang.term =
    let op_ty =
      Abstraction.Prim.get_primitive_normal_ty (Op.op_to_string op_id)
    in
    let name = Rename.name () in
    let resty = snd (NT.destruct_arrow_tp op_ty) in
    let resid : id NNtyped.typed = { x = name; ty = (None, resty) } in
    let term = Termlang.Op (op_id, List.map asts_lookup args) in
    let args = List.map NL.id_to_value args in
    let aterm =
      NL.LetOp
        {
          ret = resid;
          op = op_id;
          args;
          body = NL.value_to_term (NL.id_to_value resid);
        }
    in
    (resid, aterm, term)

  let mk_if (cond : id NNtyped.typed) (true_branch : id NNtyped.typed)
      (false_branch : id NNtyped.typed) : NL.term =
    let cond = NL.id_to_value cond in
    let e_t = NL.id_to_value true_branch |> NL.value_to_term in
    let e_f = NL.id_to_value false_branch |> NL.value_to_term in
    NL.Ite { cond; e_t; e_f }

  let apply (comp : component) (args : id NNtyped.typed list) =
    let resid, aterm, term =
      match comp with
      | Fun f -> mk_app f args (fun x -> NL.value_to_term (NL.id_to_value x))
      | Op op -> mk_op op args
      | Ctor ctor ->
          mk_ctor ctor args (fun x -> NL.value_to_term (NL.id_to_value x))
    in
    let () = Hashtbl.add asts resid.x term in
    (resid, aterm)

  let map_fst f (l, r) = (f l, r)

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

  let ut_subst (ut : UT.t) (ht : (id, id) Hashtbl.t) =
    let renamed_ty =
      List.fold_left
        (fun t name ->
          let new_name = Hashtbl.find ht name in
          Underty.T.subst_id t name new_name)
        ut (Underty.T.fv ut)
    in
    renamed_ty

  let ctx_subst ctx (ht : (id, id) Hashtbl.t) =
    List.map
      (fun (name, ty) ->
        (* foldLeft ( takes the old type, and the id, substitute if id is in old type, return the new type ) (the unsubstituted type) (the var space ) *)
        let renamed_ty =
          List.fold_left
            (fun t name ->
              let new_name = Hashtbl.find ht name in
              mmt_subst_id t name new_name)
            ty (Underty.MMT.fv ty)
        in
        let new_name = Hashtbl.find ht name in
        (new_name, renamed_ty))
      ctx

  let freshen (ctx : Typectx.ctx) =
    let ht = Hashtbl.create (List.length ctx) in
    let maybe_freshen_one (name : id) =
      if Hashtbl.mem known name then (
        Hashtbl.add ht name name;
        name)
      else
        let new_name = Rename.unique name in
        let () =
          match Hashtbl.find_opt asts name with
          | None -> failwith name
          | Some x -> ()
        in
        (* TODO: remove this since context addition checks this already ?*)
        if Hashtbl.mem ht name then failwith "duplicate key";
        Hashtbl.add ht name new_name;
        new_name
    in
    let _ = List.map (map_fst maybe_freshen_one) ctx in
    let res = ctx_subst ctx ht in
    (res, ht)
end
