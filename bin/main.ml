open Typing
open Core
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
open Tracking

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
  | RtyBase _ -> ([], rty)
  | _ -> failwith "unimplemented"

(* Largely taken straight from value_type_check::VFix *)
let handle_first_arg (a : (t, t value) typed) (rty : t rty) =
  (* Pp.printf "\nFirst Arg: %s\n" (layout_typed_value a);
     Pp.printf "\nReturn Type: %s\n" (layout_rty rty); *)
  assert (Nt.eq a.ty (Rty.erase_rty rty));
  match (a.x, rty) with
  | VFix { fixname; fixarg; _ }, RtyBaseArr { argcty; arg; retty } ->
      assert (String.equal fixarg.x arg);
      let () =
        Termcheck.init_cur_rec_func_name
          (fixname.x, Termcheck.apply_rec_arg fixarg)
      in
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
      (binding, rec_fix)
  | _ -> failwith "Did not recieve a fixpoint value and a base arrow type"

let get_synth_config_values meta_config_file =
  let open Json in
  let open Yojson.Basic.Util in
  let metaj = load_json meta_config_file in
  let bound = metaj |> member "synth_bound" |> to_int in
  let timeout = metaj |> member "synth_timeout" |> to_string in
  (bound, timeout)

let build_initial_typing_context meta_config_file : uctx =
  let prim_path = Env.get_prim_path () in

  let predefine =
    Commands.Cre.preproress meta_config_file prim_path.under_basicp ()
  in
  Pp.printf "\nPredefined:\n%s\n" (layout_structure predefine);

  let builtin_ctx = Typing.Itemcheck.gather_uctx predefine in
  Pp.printf "\nBuiltin Context:\n%s\n" (layout_typectx layout_rty builtin_ctx);

  assert (List.length predefine = List.length (Typectx.to_list builtin_ctx));

  let lemmas = Commands.Cre.preproress meta_config_file prim_path.lemmas () in

  (* TODO: There is a slightly different handling of lemmas for usingn templates*)

  (* Pp.printf "\nLemmas:\n%s\n" (layout_structure lemmas); *)
  let axioms =
    Typing.Itemcheck.gather_axioms lemmas |> List.map Mtyped._get_ty
  in
  Pp.printf "\nAxioms:\n%s\n" (List.split_by "\n" layout_prop axioms);
  let templates =
    Commands.Cre.preproress meta_config_file prim_path.templates ()
  in
  let templates = Commands.Cre.handle_template templates in
  let () = Inference.Feature.init_template templates in

  { builtin_ctx; local_ctx = Typectx.emp; axioms }

let get_args_rec_retty_body_from_source meta_config_file source_file =
  let processed_file =
    Commands.Cre.preproress meta_config_file source_file ()
  in

  assert (List.length processed_file = 2);
  Pp.printf "\nProcessed File:\n%s\n" (layout_structure processed_file);

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

  let code =
    match code.x with CVal x -> x | _ -> failwith "Did not receive a value"
  in

  let _, args, body = unfold_fix_helper code.x in
  Pp.printf "Body: %s\n" (layout_typed_term body);
  (* For other programs that use more than one arg, adjust *)
  assert (
    Core.List.for_all2_exn args argtyps ~f:(fun arg argty ->
        Nt.eq arg.ty (Rty.erase_rty argty.ty) && String.equal arg.x argty.x));

  let first_arg, rec_fix = handle_first_arg code synth_type in
  Pp.printf "\nFirst Arg: %s\n" (layout_id_rty first_arg);
  Pp.printf "\nRec Fix: %s\n" (layout_id_rty rec_fix);
  let args = first_arg :: List.tl argtyps in
  (args, rec_fix, retty, body)

let run_benchmark source_file meta_config_file =
  (* This sets up global variables pointing to the information in meta-config.json *)
  let () = Env.load_meta meta_config_file in
  let bound, timeout = get_synth_config_values meta_config_file in

  (*   Env.sexp_of_meta_config (!Env.meta_config |> Option.value_exn) |> dbg_sexp; *)
  let () =
    Z3.Params.update_param_value Backend.Smtquery.ctx "timeout" timeout
  in

  let uctx = build_initial_typing_context meta_config_file in

  let args, rec_fix, retty, body =
    get_args_rec_retty_body_from_source meta_config_file source_file
  in

  let uctx = add_to_rights uctx (rec_fix :: args) in

  let typed_code =
    Typing.Termcheck.term_type_infer uctx body |> Option.value_exn
  in

  Pp.printf "\nTyped Code:\n%s\n" (layout_rty typed_code.ty);

  (match Typing.Termcheck.term_type_check uctx body retty with
  | None -> ()
  | Some _ -> failwith "Nothing to repair");

  pprint_simple_typectx_infer uctx ("res", typed_code.ty);

  pprint_typectx_subtyping uctx.local_ctx (typed_code.ty, retty);

  Pp.printf "\nBuiltinTypingContext Before Synthesis:\n%s\n"
    (layout_typectx layout_rty uctx.builtin_ctx);
  Pp.printf "\nLocalTypingContext Before Synthesis:\n%s\n"
    (layout_typectx layout_rty uctx.local_ctx);

  let _path_props = Localization.localization uctx body retty in

  let ( (seeds : (Blocks.block * t) list),
        (components : (Pieces.component * (t list * t)) list) ) =
    Pieces.seeds_and_components uctx.builtin_ctx
  in

  let seeds = List.concat [ seeds; Pieces.seeds_from_args uctx.local_ctx ] in

  let components =
    List.concat [ components; Pieces.components_from_args uctx.local_ctx ]
  in

  Pp.printf "\nSeeds:\n%s\n"
    (List.split_by "\n"
       (fun (a, b) -> Blocks.layout_block a ^ " " ^ Nt.layout b)
       seeds);

  Pp.printf "\nComponents:\n%s\n"
    (List.split_by "\n"
       (fun (c, (args, ret)) ->
         Pieces.layout_component c ^ " : "
         ^ List.split_by "," Nt.layout args
         ^ " -> " ^ Nt.layout ret)
       components);

  let _result = Synthesis.synthesis uctx retty bound seeds components in
  print_endline "Finished Synthesis"

(** Benchmarks can be provided as a command line argument
  * Default is "sizedlist" *)
(* let regular_file =
   Command.Arg_type.create (fun filename ->
       match Sys_unix.is_file filename with
       | `Yes -> filename
       | `No -> failwith "Not a regular file"
       | `Unknown -> failwith "Could not determine if this was a regular file") *)

let regular_directory =
  Command.Arg_type.create (fun directory ->
      match Sys_unix.is_directory directory with
      | `Yes -> directory
      | `No -> failwith "Not a regular directory"
      | `Unknown ->
          failwith "Could not determine if this was a regular directory")

let cobb_synth =
  Command.basic ~summary:"TODO"
    Command.Let_syntax.(
      let%map_open benchmark_dir = anon ("benchmark_dir" %: regular_directory)
      and program_name =
        anon ("program_name" %: Command.Arg_type.create (fun x -> x))
      in
      fun () ->
        let source_file = Core.Filename.concat benchmark_dir program_name in
        let meta_config_file =
          Core.Filename.concat benchmark_dir "meta-config.json"
        in
        let _ = run_benchmark source_file meta_config_file in
        ())

let prog = Command.group ~summary:"Cobb" [ ("synthesis", cobb_synth) ]
let () = Command_unix.run prog

(* let () =
   run_benchmark benchmark_to_run.source_file benchmark_to_run.meta_config_file
     benchmark_to_run.bound *)
