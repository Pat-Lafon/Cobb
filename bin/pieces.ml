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

  let seeds_and_components (libs : (id * UT.t) list) =
    (* I move this inside of a function becuase `Abstraction.Prim_map.get_normal_m` will call some global reference that hasn't been set yet *)
    (* Main sets this ref, but this file gets built first *)
    let prim_seeds, operations = prim_gathering_helper () in
    let lib_seeds, funs = library_gathering_helper libs in
    let seeds = prim_seeds @ lib_seeds @ builtin_seeds in
    (seeds, operations @ funs)

  let mk_app (f_id : id NNtyped.typed) (args : id NNtyped.typed list) k :
      id NNtyped.typed * NL.term =
    let name = Rename.name () in
    let resty = snd (NT.destruct_arrow_tp (snd f_id.ty)) in
    let resid : id NNtyped.typed = { x = name; ty = (None, resty) } in
    let args = List.map NL.id_to_value args in
    (resid, NL.LetApp { ret = resid; f = f_id; args; body = k resid })

  let mk_ctor (ctor : id NNtyped.typed) (args : id NNtyped.typed list) k :
      id NNtyped.typed * NL.term =
    let name = Rename.name () in
    let resty = snd (NT.destruct_arrow_tp (snd ctor.ty)) in
    let resid : id NNtyped.typed = { x = name; ty = (None, resty) } in
    let args = List.map NL.id_to_value args in
    (resid, NL.LetDtConstructor { ret = resid; f = ctor; args; body = k resid })

  let mk_op (op_id : Op.op) (args : id NNtyped.typed list) :
      id NNtyped.typed * NL.term =
    let op_ty =
      Abstraction.Prim.get_primitive_normal_ty (Op.op_to_string op_id)
    in
    let name = Rename.name () in
    let resty = snd (NT.destruct_arrow_tp op_ty) in
    let resid : id NNtyped.typed = { x = name; ty = (None, resty) } in
    let args = List.map NL.id_to_value args in
    ( resid,
      NL.LetOp
        {
          ret = resid;
          op = op_id;
          args;
          body = NL.value_to_term (NL.id_to_value resid);
        } )

  let mk_if (cond : id NNtyped.typed) (true_branch : id NNtyped.typed)
      (false_branch : id NNtyped.typed) : NL.term =
    let cond = NL.id_to_value cond in
    let e_t = NL.id_to_value true_branch |> NL.value_to_term in
    let e_f = NL.id_to_value false_branch |> NL.value_to_term in
    NL.Ite { cond; e_t; e_f }

  let apply (comp : component) (args : id NNtyped.typed list) =
    match comp with
    | Fun f -> mk_app f args (fun x -> NL.value_to_term (NL.id_to_value x))
    | Op op -> mk_op op args
    | Ctor ctor ->
        mk_ctor ctor args (fun x -> NL.value_to_term (NL.id_to_value x))
end
