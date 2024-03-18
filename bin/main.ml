open Typing
open Core
open Assertion
open Sugar
open Term
open Pieces
open Blocks
open Localization
open Utils
open Frontend_opt.To_typectx
open Language.FrontendTyped
open Zzdatatype.Datatype
open Mtyped
open Rty
open Cty

type synth_input = {
  name : string;
  source_file : string;
  meta_config_file : string;
  bound : int;
}

let benchmarks =
  [
    {
      name = "sizedlist1";
      source_file = "data/benchmark/sizedlist/prog1.ml";
      meta_config_file = "data/benchmark/sizedlist/meta-config.json";
      bound = 0;
    };
    {
      name = "sizedlist2";
      source_file = "data/benchmark/sizedlist/prog2.ml";
      meta_config_file = "data/benchmark/sizedlist/meta-config.json";
      bound = 1;
    };
    {
      name = "sizedlist3";
      source_file = "data/benchmark/sizedlist/prog3.ml";
      meta_config_file = "data/benchmark/sizedlist/meta-config.json";
      bound = 1;
    };
    {
      name = "sortedlist";
      source_file =
        "underapproximation_type/data/benchmark/quickchick/sortedlist/prog.ml";
      meta_config_file = "meta-config.json";
      bound = 3;
    };
    {
      name = "sizedtree";
      source_file =
        "underapproximation_type/data/benchmark/quickchick/sizedtree/prog.ml";
      meta_config_file = "meta-config.json";
      bound = 3;
    };
    {
      name = "uniquel";
      source_file = "underapproximation_type/data/benchmark/uniquel/prog.ml";
      meta_config_file = "meta-config.json";
      bound = 3;
    };
    {
      name = "sizedtree";
      source_file =
        "underapproximation_type/data/benchmark/quickchick/sizedtree/prog.ml";
      meta_config_file = "meta-config.json";
      bound = 3;
    };
    {
      name = "rbtree";
      source_file =
        "underapproximation_type/data/benchmark/quickchick/rbtree/prog.ml";
      meta_config_file = "meta-config.json";
      bound = 3;
    };
  ]

(* Assumes argument is a fixpoint value *)
let unfold_fix_helper (fix : _ value) : _ * _ list * _ typed =
  (* Unwrap the function into a recursive call *)
  let[@warning "-8"] (VFix { fixname; fixarg; body }) = (fix [@warning "+8"]) in
  (* Handle any other arguments *)
  let rec aux (n : _ typed) =
    match n.x with
    | CVal { x = VLam { lamarg; body }; _ } ->
        let other_args, body = aux body in
        (lamarg :: other_args, body)
    | _ -> ([], n)
  in
  let other_args, body = aux body in
  (fixname, fixarg :: other_args, body)

let rec unfold_rty_helper rty : _ typed list * _ rty =
  match rty with
  (* | RtyArrArr { argrty : 't rty; retty : 't rty } ->
      let other_args, retty = unfold_rty_helper retty in
      (argrty :: other_args, retty) *)
  | RtyBaseArr { argcty : 't cty; arg : (string[@bound]); retty : 't rty } ->
      let other_args, retty = unfold_rty_helper retty in
      ((arg #: (RtyBase { ou = true; cty = argcty })) :: other_args, retty)
  | RtyBase { ou : bool; cty : 't cty } -> ([], rty)
  | _ -> failwith "unimplemented"

(* Largely taken straight from value_type_check::VFix *)
let handle_first_arg (a : (t, t value) typed) (rty : t rty) =
  (* Pp.printf "\nFirst Arg: %s\n" (layout_typed_value a);
     Pp.printf "\nReturn Type: %s\n" (layout_rty rty); *)
  assert (Nt.eq a.ty (Rty.erase_rty rty));
  match (a.x, rty) with
  | VFix { fixname; fixarg; body }, RtyBaseArr { argcty; arg; retty } ->
      assert (String.equal fixarg.x arg);
      let a = { x = Rename.unique fixarg.x; ty = fixarg.ty } in
      let _ : identifier = NameTracking.known_var a in
      (*       Pp.printf "\nFirst Arg: %s\n" a.x; *)
      let prop = Checkaux.make_order_constraint fixarg a in
      (*       Pp.printf "\nProp: %s\n" (layout_prop prop); *)
      let retty_a = subst_rty_instance arg (AVar a) retty in
      (*       Pp.printf "\nSubstituted Return Type: %s\n" (layout_rty retty_a); *)
      let rty_a = RtyBaseArr { argcty; arg = a.x; retty = retty_a } in
      (*       Pp.printf "\nRty A: %s\n" (layout_rty rty_a); *)
      let rty_a = map_prop_in_retrty (smart_add_to prop) rty_a in
      (*       Pp.printf "\nRty A: %s\n" (layout_rty rty_a); *)
      let binding = fixarg.x #: (RtyBase { ou = true; cty = argcty }) in
      (*       Pp.printf "\nBinding: %s\n" (layout_id_rty binding); *)
      assert (String.equal arg fixarg.x);
      (*
        So long as these are equal, the next line doesn't really do anything I
        think? I should double check. Otherwise, return this as the new type we
        are targetting
      *)
      let _retty = subst_rty_instance arg (AVar fixarg) retty in
      (*       Pp.printf "\nSubstituted Return Type: %s\n" (layout_rty _retty); *)
      assert (
        Sexp.( = )
          (Rty.sexp_of_rty Nt.sexp_of_t _retty)
          (Rty.sexp_of_rty Nt.sexp_of_t retty));
      let rec_fix = fixname.x #: rty_a in
      (*       Pp.printf "\nRec Fix: %s\n" (layout_id_rty rec_fix); *)
      (binding, rec_fix)
  | _ -> failwith "Did not recieve a fixpoint value and a base arrow type"

let run_benchmark source_file meta_config_file bound =
  (* This sets up global variables pointing to the information in meta-config.json *)
  let () = Env.load_meta meta_config_file in

  (*   Env.sexp_of_meta_config (!Env.meta_config |> Option.value_exn) |> dbg_sexp; *)
  let () = Z3.Params.update_param_value Backend.Smtquery.ctx "timeout" "4999" in
  let processed_file =
    Commands.Cre.preproress meta_config_file source_file ()
  in

  assert (List.length processed_file = 2);
  Pp.printf "\nProcessed File:\n%s\n" (layout_structure processed_file);
  let prim_path = Env.get_prim_path () in

  let predefine =
    Commands.Cre.preproress meta_config_file prim_path.under_basicp ()
  in
  Pp.printf "\nPredefined:\n%s\n" (layout_structure predefine);

  let builtin_ctx = Typing.Itemcheck.gather_uctx predefine in
  Pp.printf "\nBuiltin Context:\n%s\n" (layout_typectx layout_rty builtin_ctx);

  (let (Typectx x) = builtin_ctx in
   assert (List.length predefine = List.length x));

  let lemmas = Commands.Cre.preproress meta_config_file prim_path.lemmas () in

  (* Pp.printf "\nLemmas:\n%s\n" (layout_structure lemmas); *)
  let axioms =
    Typing.Itemcheck.gather_axioms lemmas
    |> List.map (fun ({ x; ty } : _ typed) -> ty)
  in
  Pp.printf "\nAxioms:\n%s\n" (List.split_by "\n" layout_prop axioms);

  let uctx : uctx = { builtin_ctx; local_ctx = Typectx.emp; axioms } in

  let synth_name, synth_type =
    List.find_map
      (fun item ->
        match item with
        | Item.MRty { name; is_assumption; rty } ->
            assert (not is_assumption);
            Some (name, rty)
        | _ -> None)
      processed_file
    |> Option.value_exn
  in
  Pp.printf "\nSynthesis Problem: %s:%s\n" synth_name (layout_rty synth_type);

  let argtyps, retty = unfold_rty_helper synth_type in
  Pp.printf "\nArg Types: %s\n" (List.split_by "," layout_id_rty argtyps);
  Pp.printf "\nReturn Type: %s\n" (layout_rty retty);

  let code =
    List.find_map
      (fun item ->
        match item with
        | Item.MFuncImp { name = { x; _ }; if_rec = true; body }
          when String.equal x synth_name ->
            Some body
        | _ -> None)
      processed_file
    |> Option.value_exn
  in

  (* let _ =
       Typing.Termcheck.term_type_check uctx code synth_type |> Option.value_exn
     in *)

  (*   Pp.printf "\nCode:\n%s\n" (layout_typed_term code); *)
  let code =
    match code.x with CVal x -> x | _ -> failwith "Did not receive a value"
  in

  let _, args, body = unfold_fix_helper code.x in
  (* For other programs that use more than one arg, adjust *)
  assert (List.length args = 1);
  assert (
    Core.List.for_all2_exn args argtyps ~f:(fun arg argty ->
        Nt.eq arg.ty (Rty.erase_rty argty.ty) && String.equal arg.x argty.x));

  (* let retty = subst_rty_instance fstarg.x (Lit.AVar decreasing_arg) retty in
     Pp.printf "\nSubstituted Return Type: %s\n" (layout_rty retty); *)
  let first_arg, rec_fix = handle_first_arg code synth_type in
  Pp.printf "\nFirst Arg: %s\n" (layout_id_rty first_arg);
  Pp.printf "\nRec Fix: %s\n" (layout_id_rty rec_fix);

  let uctx = add_to_rights uctx [ first_arg; rec_fix ] in

  Pp.printf "Body: %s\n" (layout_typed_term body);

  let typed_code =
    Typing.Termcheck.term_type_infer uctx body |> Option.value_exn
  in

  Pp.printf "\nTyped Code:\n%s\n" (layout_rty typed_code.ty);

  (* let res_term =
       Typing.Termcheck.term_type_check uctx body retty |> Option.value_exn
     in *)
  Pp.printf "\nTyped Code:\n%s\n" (layout_rty typed_code.ty);

  pprint_simple_typectx_infer uctx ("res", typed_code.ty);

  pprint_typectx_subtyping uctx.local_ctx (typed_code.ty, retty);

  (*
  assert (Subtyping.Subrty.sub_rty_bool uctx (typed_code.ty, retty)); *)
  let path_props = Localization.localization uctx body retty in

  (* let seeds, components = Pieces.seeds_and_components libs in *)

  (*
     let args = decreasing_arg :: List.tl args in

     let seeds = List.append seeds (List.map Pieces.mk_var args) in *)

  (*

     let seeds =
       List.map
         (fun ((id, term), ty) : (Blocks.block * ty) ->
           let ut = Typecheck.Undercheck.term_type_infer uctx term in
           let mmt = MMT.UtNormal ut in
           let seed_utx = Typectx.ut_force_add_to_right ctx'' (id, mmt) in
           let term_ty = term.ty in
           (({ x = id; ty = term_ty }, Ut mmt, seed_utx), ty))
         seeds
     in
  *)
  (* todo Add argument variables to seeds *)

  (* Add Recursive Componenet*)
  (* let nty = UT.erase f.ty in
     let argtys, resty = NT.destruct_arrow_tp nty in
     let recursive_piece : Pieces.component = Fun { x = f.x; ty = (None, nty) } in
     let components = (recursive_piece, (argtys, resty)) :: components in
  *)
  Pp.printf "\nBuiltinTypingContext Before Synthesis:\n%s\n"
    (layout_typectx layout_rty uctx.builtin_ctx);
  Pp.printf "\nLocalTypingContext Before Synthesis:\n%s\n"
    (layout_typectx layout_rty uctx.local_ctx);

  let ( (seeds : (Blocks.block * t) list),
        (components : (Pieces.component * (t list * t)) list) ) =
    Pieces.seeds_and_components uctx.builtin_ctx
  in

  let seeds = List.concat [ seeds; Pieces.seeds_from_args uctx.local_ctx ] in

  Pp.printf "\nSeeds:\n%s\n"
    (List.split_by "\n"
       (fun (a, b) -> Blocks.layout_block a ^ " " ^ Nt.layout b)
       seeds);

  Pp.printf "\nComponents:\n%s\n"
    (List.split_by "\n" (fun (c, _) -> Pieces.layout_component c) components);

  let result = Synthesis.synthesis uctx retty bound seeds components in
  print_endline "Finished Synthesis"

(** Benchmarks can be provided as a command line argument
  * Default is "sizedlist" *)
let benchmark_name =
  if Int.equal (Array.length (Sys.get_argv ())) 1 then "sizedlist1"
  else (Sys.get_argv ()).(1)

let benchmark_to_run =
  List.find __FILE__ (fun x -> String.equal x.name benchmark_name) benchmarks

let () =
  run_benchmark benchmark_to_run.source_file benchmark_to_run.meta_config_file
    benchmark_to_run.bound
