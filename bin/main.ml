open Typing
open Term
open Pieces
open Blocks
open Blockmap
open Block
open Localization
open Language.FrontendTyped
open Zzdatatype.Datatype
open Mtyped
open Rty
open Cty
open Tracking
open Synthesiscollection
module Env = Zzenv

let rec unfold_rty_helper rty : _ typed list * _ rty =
  match rty with
  (* | RtyArrArr { argrty : 't rty; retty : 't rty } ->
      let other_args, retty = unfold_rty_helper retty in
      (argrty :: other_args, retty) *)
  | RtyBaseArr { argcty : 't cty; arg : (string[@bound]); retty : 't rty } ->
      let other_args, retty = unfold_rty_helper retty in
      ((arg #: (RtyBase { ou = true; cty = argcty })) :: other_args, retty)
  | RtyBase _ -> ([], rty)
  | _ -> failwith "unfold_rty_helper::error"

let rec strip_lam (t : (t, t term) typed) : (t, t term) typed =
  match t.x with
  | CVal { x = VLam { lamarg; body }; _ } -> strip_lam body
  | _ -> t

(* Largely taken straight from value_type_check::VFix *)
let handle_recursion_args (a : (t, t value) typed) (rty : t rty) =
  assert (Nt.eq a.ty (Rty.erase_rty rty));
  match (a.x, rty) with
  | VFix { fixname; fixarg; body }, RtyBaseArr { argcty; arg; retty } ->
      assert (String.equal fixarg.x arg);

      if
        String.equal "stlc_term"
          (Nt.destruct_arr_tp fixname.ty |> snd |> Nt.layout)
      then
        match (body.x, retty) with
        | ( CVal { x = VLam { lamarg; body }; _ },
            RtyBaseArr { argcty = argcty1; arg = arg1; retty } ) ->
            let rty' =
              let arg' = { x = Rename.unique arg; ty = fixarg.ty } in
              let arg = arg #: fixarg.ty in
              let arg1' = { x = Rename.unique arg1; ty = lamarg.ty } in
              let arg1 = arg1 #: lamarg.ty in
              let rec_constraint_cty = Termcheck.apply_rec_arg2 arg arg' arg1 in
              RtyBaseArr
                {
                  argcty;
                  arg = arg'.x;
                  retty =
                    RtyBaseArr
                      {
                        argcty = intersect_ctys [ argcty1; rec_constraint_cty ];
                        arg = arg1'.x;
                        retty =
                          subst_rty_instance arg1.x (AVar arg1')
                          @@ subst_rty_instance arg.x (AVar arg') retty;
                      };
                }
            in
            let binding = arg #: (RtyBase { ou = true; cty = argcty }) in
            let binding1 = arg1 #: (RtyBase { ou = true; cty = argcty1 }) in
            let body =
              body
              #-> (subst_term_instance fixarg.x (VVar arg #: fixarg.ty))
              #-> (subst_term_instance lamarg.x (VVar arg1 #: fixarg.ty))
            in

            let rec_fix = fixname.x #: rty' in
            ([ binding; binding1 ], rec_fix, strip_lam body)
        | _ -> failwith "unexpected lack of second argument for stlc lam term"
      else
        let retty = subst_rty_instance arg (AVar fixarg) retty in

        let rec_constraint_cty = Termcheck.apply_rec_arg1 fixarg in
        (* Termcheck.apply_rec_arg2 *)
        let () =
          Termcheck.init_cur_rec_func_name (fixname.x, rec_constraint_cty)
        in
        let rty' =
          let a = { x = Rename.unique fixarg.x; ty = fixarg.ty } in
          RtyBaseArr
            {
              argcty = intersect_ctys [ argcty; rec_constraint_cty ];
              arg = a.x;
              retty =
                subst_rty_instance arg (AVar (NameTracking.known_var a)) retty;
            }
        in
        (*       Pp.printf "\nSubstituted Return Type: %s\n" (layout_rty retty_a); *)
        (*       Pp.printf "\nRty A: %s\n" (layout_rty rty_a); *)
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
          Core.Sexp.( = )
            (Rty.sexp_of_rty Nt.sexp_of_t _retty)
            (Rty.sexp_of_rty Nt.sexp_of_t retty));
        let rec_fix = fixname.x #: rty' in

        ([ binding ], rec_fix, strip_lam body)
  | _ -> failwith "Did not recieve a fixpoint value and a base arrow type"

type config = {
  bound : int;
  res_ext : string;
  abd_ext : string;
  syn_ext : string;
  syn_rlimit : int;
  abd_rlimit : int;
  use_missing_coverage_file : bool;
  collect_ext : string;
  component_list : string list;
}

let get_synth_config_values meta_config_file : config =
  let open Json in
  let open Yojson.Basic.Util in
  let metaj = load_json meta_config_file in
  let bound = metaj |> member "synth_bound" |> to_int in
  let timeout = metaj |> member "synth_timeout" |> to_string_option in
  assert (timeout = None);
  let res_ext = metaj |> member "resfile" |> to_string in
  let abd_ext = metaj |> member "abdfile" |> to_string in
  let syn_ext = metaj |> member "synfile" |> to_string in
  let syn_rlimit = metaj |> member "synth_rlimit" |> to_int in
  let abd_rlimit = metaj |> member "abduce_rlimit" |> to_int in
  let collect_ext = metaj |> member "collectfile" |> to_string in
  let comp_path = metaj |> member "comp_path" |> to_string in
  let use_missing_coverage_file =
    metaj
    |> member "use_missing_coverage_file"
    |> to_bool_option
    |> Option.value ~default:false
  in

  assert (abd_rlimit >= syn_rlimit);

  let comp_path =
    Filename.concat (Filename.dirname meta_config_file) comp_path
  in

  let component_list = Core.In_channel.read_lines comp_path in

  {
    bound;
    res_ext;
    abd_ext;
    syn_ext;
    abd_rlimit;
    syn_rlimit;
    collect_ext;
    component_list;
    use_missing_coverage_file;
  }

let build_initial_typing_context () : uctx =
  let prim_path = Env.get_prim_path () in

  let predefine = Commands.Cre.preprocess prim_path.coverage_typing () in

  (*   Pp.printf "\nPredefined:\n%s\n" (layout_structure predefine); *)
  let builtin_ctx = Typing.Itemcheck.gather_uctx predefine in

  (*   Pp.printf "\nBuiltin Context:\n%s\n" (layout_typectx layout_rty builtin_ctx); *)
  assert (List.length predefine = List.length (Typectx.to_list builtin_ctx));

  let lemmas = Commands.Cre.preprocess prim_path.axioms () in

  (* Pp.printf "\nLemmas:\n%s\n" (layout_structure lemmas); *)
  let axioms =
    Typing.Itemcheck.gather_axioms lemmas |> List.map Mtyped._get_ty
  in

  { builtin_ctx; local_ctx = Typectx.emp; axioms }

let rec swap_in_body (code : (Nt.t, Nt.t value) typed) :
    (t, t term) typed -> (Nt.t, Nt.t value) typed =
  match code.x with
  | VFix { fixname; fixarg; body = { x = CVal body; ty } } ->
      fun x ->
        let b : _ -> (Nt.t, Nt.t value) typed = swap_in_body body in
        (VFix { fixname; fixarg; body = b x |> value_to_term }) #: code.ty
  | VFix { fixname; fixarg; body } -> (
      fun x : (Nt.t, Nt.t value) typed ->
        (VFix { fixname; fixarg; body = x }) #: code.ty)
  | VLam { lamarg; body = { x = CVal body; ty } } ->
      fun x ->
        let b : _ -> (Nt.t, Nt.t value) typed = swap_in_body body in
        (VLam { lamarg; body = b x |> value_to_term }) #: code.ty
  | VLam { lamarg; body } -> (
      fun x : (Nt.t, Nt.t value) typed -> (VLam { lamarg; body = x }) #: code.ty
      )
  | _ -> failwith "swap_in_body::failure"

let get_args_rec_retty_body_from_source source_file =
  let processed_file = Commands.Cre.preprocess source_file () in

  assert (List.length processed_file = 2);

  (*  Pp.printf "\nProcessed File:\n%s\n" (layout_structure processed_file); *)
  let synth_name, synth_type =
    List.find_map
      (fun item ->
        match item with
        | Item.MRty { name; is_assumption; rty } ->
            assert (not is_assumption);
            Some (name, rty)
        | _ -> None)
      processed_file
    |> Option.get
  in

  (*   Pp.printf "\nSynthesis Problem: %s:%s\n" synth_name (layout_rty synth_type); *)
  let argtyps, retty = unfold_rty_helper synth_type in

  (* Pp.printf "\nArg Types: %s\n" (List.split_by "," layout_id_rty argtyps);
     Pp.printf "\nReturn Type: %s\n" (layout_rty retty); *)
  let code =
    List.find_map
      (fun item ->
        match item with
        | Item.MFuncImp { name = { x; _ }; if_rec = true; body }
          when String.equal x synth_name ->
            Some body
        | _ -> None)
      processed_file
    |> Option.get
  in

  let code =
    match code.x with CVal x -> x | _ -> failwith "Did not receive a value"
  in

  let reconstruct_code_with_new_body x =
    let b = swap_in_body code in
    Item.MFuncImp
      {
        name = synth_name #: (erase_rty synth_type);
        if_rec = true;
        body = b x |> value_to_term;
      }
  in

  let first_arg, rec_fix, body = handle_recursion_args code synth_type in
  (* Pp.printf "Body: %s\n" (layout_typed_term body);
     List.iter (fun x -> Pp.printf "\nArg: %s\n" (layout_id_rty x)) first_arg;
     Pp.printf "\nRec Fix: %s\n" (layout_id_rty rec_fix); *)
  let args =
    first_arg
    @ List.sublist argtyps ~start_included:(List.length first_arg)
        ~end_excluded:(List.length argtyps)
  in
  (args, rec_fix, retty, body, reconstruct_code_with_new_body)

let rec remove_excess_ast_aux (t : (Nt.t, Nt.t term) typed) =
  match t.x with
  | CErr | CApp _ | CAppOp _ | CVal _ -> t
  | CLetE
      {
        lhs;
        rhs =
          {
            x =
              CApp
                {
                  appf = { x = VVar { x = "bool_gen"; _ }; _ };
                  apparg = { x = VConst U; _ };
                };
            _;
          };
        body =
          {
            x =
              CMatch
                {
                  matched = { x = VVar v; _ };
                  match_cases =
                    [
                      CMatchcase
                        { constructor = { x = "True"; _ }; args = []; exp };
                      CMatchcase
                        {
                          constructor = { x = "False"; _ };
                          args = [];
                          exp = { x = CVal { x = VVar f; _ }; _ };
                        };
                    ];
                };
            _;
          };
      }
    when Core.String.(lhs.x = v.x && is_prefix f.x ~prefix:"Hole") ->
      (* let _ = layout_typed_term t |> print_endline in
         let _ = f.x |> print_endline in *)
      remove_excess_ast_aux exp
  | CLetE (* True branch Err *)
      {
        lhs;
        rhs =
          {
            x =
              CApp
                {
                  appf = { x = VVar { x = "bool_gen"; _ }; _ };
                  apparg = { x = VConst U; _ };
                };
            _;
          };
        body =
          {
            x =
              CMatch
                {
                  matched = { x = VVar v; _ };
                  match_cases =
                    [
                      CMatchcase
                        {
                          constructor = { x = "True"; _ };
                          args = [];
                          exp = { x = CErr; _ };
                        };
                      CMatchcase
                        { constructor = { x = "False"; _ }; args = []; exp };
                    ];
                };
            _;
          };
      }
    when Core.String.(lhs.x = v.x) ->
      remove_excess_ast_aux exp
  | CLetE (* False branch Err *)
      {
        lhs;
        rhs =
          {
            x =
              CApp
                {
                  appf = { x = VVar { x = "bool_gen"; _ }; _ };
                  apparg = { x = VConst U; _ };
                };
            _;
          };
        body =
          {
            x =
              CMatch
                {
                  matched = { x = VVar v; _ };
                  match_cases =
                    [
                      CMatchcase
                        { constructor = { x = "True"; _ }; args = []; exp };
                      CMatchcase
                        {
                          constructor = { x = "False"; _ };
                          args = [];
                          exp = { x = CErr; _ };
                        };
                    ];
                };
            _;
          };
      }
    when Core.String.(lhs.x = v.x) ->
      remove_excess_ast_aux exp
  | CLetE { lhs; rhs = { x = CVal { x = VVar v; _ }; _ }; body } when lhs = v ->
      remove_excess_ast_aux body
  | CLetE { lhs; rhs; body } ->
      (CLetE { lhs; rhs; body = remove_excess_ast_aux body }) #: t.ty
  | CLetDeTu { turhs; tulhs; body } ->
      (CLetDeTu { turhs; tulhs; body = remove_excess_ast_aux body }) #: t.ty
  | CMatch { matched; match_cases } ->
      (CMatch
         {
           matched;
           match_cases =
             List.map
               (fun (CMatchcase { constructor; args; exp }) ->
                 CMatchcase
                   { constructor; args; exp = remove_excess_ast_aux exp })
               match_cases;
         })
      #: t.ty

let rec nd_join_list (t : (t, t term) typed list) : (t, t term) typed =
  match t with
  | [] -> failwith "Empty list"
  | [ x ] -> x
  | x :: xs -> Pieces.mk_ND_choice x (nd_join_list xs)

(** Take the body of the function, a lambda to convert the body into full code,
  and output it somewhere after some cleanup.  *)
let final_program_to_string (reconstruct_code_with_new_body : _ -> _) new_body :
    string =
  let new_frontend_prog =
    new_body |> reconstruct_code_with_new_body |> Item.map_item (fun x -> None)
  in

  Frontend_opt.To_item.layout_item new_frontend_prog

let set_z3_rlimit rlimit =
  Z3.Params.update_param_value Backend.Smtquery.ctx "rlimit"
    (string_of_int rlimit)

let check_config _ meta_config_file =
  let _ = get_synth_config_values meta_config_file in
  ()

let abduce_benchmark source_file meta_config_file =
  let config = get_synth_config_values meta_config_file in

  set_z3_rlimit config.abd_rlimit;

  let missing_coverage =
    Commands.Cre.type_infer_inner meta_config_file source_file ()
  in

  let abduction_file = source_file ^ config.abd_ext in

  if Sys_unix.is_file_exn abduction_file then
    let previous_coverage = Core.In_channel.read_all abduction_file in
    let current_coverage = layout_rty missing_coverage in
    assert (String.equal previous_coverage current_coverage)
  else
    Core.Out_channel.write_all abduction_file
      ~data:(layout_rty missing_coverage)

let synthesis_benchmark source_file meta_config_file =
  let config = get_synth_config_values meta_config_file in

  let start_time = Sys.time () in

  let missing_coverage =
    if config.use_missing_coverage_file then (
      let open Language in
      (* Basically do all of the initialization since we aren't running the
         abduction algorithm to do this for us *)
      let () = Env.load_meta meta_config_file in
      let prim_path = Env.get_prim_path () in
      let templates = Commands.Cre.preprocess prim_path.templates () in
      let templates = Commands.Cre.handle_template templates in
      let missing_type_filename = source_file ^ ".missing" in

      (* Process actual file*)
      let missing_type_code =
        Commands.Cre.preprocess missing_type_filename ()
      in

      assert (List.length missing_type_code == 1);

      let _, missing_rty = get_rty_by_name missing_type_code "missing_ty" in

      print_endline
        "Pulled a missing coverage type from file because of config flag";
      print_endline (layout_rty missing_rty);

      unfold_rty_helper missing_rty |> snd)
    else (
      set_z3_rlimit config.abd_rlimit;

      Commands.Cre.type_infer_inner meta_config_file source_file ())
  in

  print_endline ("Components" ^ String.concat "," config.component_list);

  Printf.printf "Missing Coverage: %s\n" (layout_rty missing_coverage);

  if Utils.rty_is_false missing_coverage then failwith "No missing coverage";

  set_z3_rlimit config.syn_rlimit;

  let collection_file = source_file ^ config.collect_ext in

  (*   Env.sexp_of_meta_config (!Env.meta_config |> Option.value_exn) |> dbg_sexp; *)
  let uctx = build_initial_typing_context () in

  let args, rec_fix, retty, body, reconstruct_code_with_new_body =
    get_args_rec_retty_body_from_source source_file
  in

  let uctx = add_to_rights uctx (rec_fix :: args) in

  Pp.printf "\nBuiltinTypingContext Before Synthesis:\n%s\n"
    (Frontend_opt.To_typectx.layout_typectx layout_rty uctx.builtin_ctx);
  Pp.printf "\nLocalTypingContext Before Synthesis:\n%s\n"
    (Frontend_opt.To_typectx.layout_typectx layout_rty uctx.local_ctx);

  (match Typing.Termcheck.term_type_check uctx body retty with
  | None -> ()
  | Some _ -> failwith "Nothing to repair");

  Context.set_global_uctx uctx;

  let _typed_code = Typing.Termcheck.term_type_infer uctx body |> Option.get in

  (*   Pp.printf "\nTyped Code:\n%s\n" (layout_rty typed_code.ty); *)
  (* pprint_simple_typectx_infer uctx ("res", typed_code.ty);

     pprint_typectx_subtyping uctx.local_ctx (typed_code.ty, retty);
  *)
  (* Pp.printf "\nBuiltinTypingContext Before Synthesis:\n%s\n"
       (Frontend_opt.To_typectx.layout_typectx layout_rty uctx.builtin_ctx);
     Pp.printf "\nLocalTypingContext Before Synthesis:\n%s\n"
       (Frontend_opt.To_typectx.layout_typectx layout_rty uctx.local_ctx); *)
  assert (
    not (Typing.Termcheck.term_type_check uctx body retty |> Option.is_some));
  assert (Subtyping.Subrty.sub_rty_bool uctx (retty, missing_coverage));

  let ( (seeds : Block.t list),
        (components : (Pieces.component * (t list * t)) list) ) =
    Pieces.seeds_and_components uctx.builtin_ctx config.component_list
  in

  let seeds = List.concat [ seeds; Pieces.seeds_from_args uctx.local_ctx ] in

  let components =
    List.concat [ components; Pieces.components_from_args uctx.local_ctx ]
  in

  let path_maps, new_body =
    Localization.localization uctx body missing_coverage
  in

  print_endline ("Number of paths: " ^ string_of_int (List.length path_maps));

  let context_maps =
    List.fold_left
      (fun acc (a, b, _) ->
        assert (not (Hashtbl.mem acc a));
        Hashtbl.replace acc a b;
        acc)
      (Hashtbl.create 5) path_maps
  in
  let substitution_maps = List.map (fun (a, _, c) -> (a, c)) path_maps in

  let raw_body = Anf_to_raw_term.typed_term_to_typed_raw_term new_body in

  (*   Printf.printf "Missing Coverage: %s\n" (layout_rty missing_coverage); *)

  (* Pp.printf "\nSeeds:\n%s\n"
          (List.split_by "\n"
             (fun (a, b) -> Block.layout a ^ " " ^ Nt.layout b)
             seeds);

     Pp.printf "\nComponents:\n%s\n"
       (List.split_by "\n"
          (fun (c, (args, ret)) ->
            Pieces.layout_component c ^ " : "
            ^ List.split_by "," Nt.layout args
            ^ " -> " ^ Nt.layout ret)
          components); *)
  (* failwith "stop here"; *)
  let inital_map = BlockMap.init seeds in

  let init_synth_col = SynthesisCollection.init inital_map context_maps in

  let synthesis_result =
    PrioritySynthesis.synthesis missing_coverage config.bound init_synth_col
      components collection_file
  in

  let synthesis_result =
    synthesis_result
    |> List.map (fun (a, b) -> (a, nd_join_list (List.map (fun b -> b) b)))
  in

  let new_body =
    substitution_maps
    |> List.fold_left
         (fun acc (lc, s) ->
           match List.assoc_opt lc synthesis_result with
           | None -> acc
           | Some synth_repair ->
               Raw_term.typed_subst_raw_term s
                 (fun _ -> (Anf_to_raw_term.denormalize_term synth_repair).x)
                 acc)
         raw_body
    |> Raw_term_to_anf.normalize_term |> remove_excess_ast_aux
    |> remove_excess_ast_aux
  in

  print_endline ("New_body :\n" ^ layout_typed_term new_body);

  set_z3_rlimit config.abd_rlimit;

  let result =
    Typing.Termcheck.term_type_check uctx new_body retty |> Option.is_some
  in
  if not result then failwith "Failed to type check result";

  let total_time = Sys.time () -. start_time in

  let synthesized_program =
    final_program_to_string reconstruct_code_with_new_body new_body
  in

  let abduction_file = source_file ^ config.abd_ext in
  let synthesis_file = source_file ^ config.syn_ext in
  let results_file = source_file ^ config.res_ext ^ ".csv" in

  let results_csv_contents =
    Printf.sprintf
      "Result, Bounds, Resource Limit, Queries, Total Time\n\
       %b, %d, %d, %d, %.2f" result config.bound config.syn_rlimit
      !Backend.Check.query_counter
      total_time
  in
  Core.Out_channel.write_all results_file ~data:results_csv_contents;
  Core.Out_channel.write_all synthesis_file ~data:synthesized_program;
  Core.Out_channel.write_all abduction_file ~data:(layout_rty missing_coverage);

  print_endline "Finished Synthesis"

(** Benchmarks can be provided as a command line argument
  * Default is "sizedlist" *)
let regular_file =
  Command.Arg_type.create (fun filename ->
      match Sys_unix.is_file filename with
      | `Yes -> filename
      | `No -> failwith "Not a regular file"
      | `Unknown -> failwith "Could not determine if this was a regular file")

let regular_directory =
  Command.Arg_type.create (fun directory ->
      match Sys_unix.is_directory directory with
      | `Yes -> directory
      | `No -> failwith "Not a regular directory"
      | `Unknown ->
          failwith "Could not determine if this was a regular directory")

let cobb (f : string -> string -> unit) =
  Command.basic ~summary:"The Cobb synthesizer which leverages coverage types"
    Command.Let_syntax.(
      (* let%map_open benchmark_dir = anon ("benchmark_dir" %: regular_directory)
         and program_name =
           anon ("program_name" %: Command.Arg_type.create (fun x -> x))
         in *)
      let%map_open source_file = anon ("program" %: regular_file) in
      fun () ->
        Memtrace.trace_if_requested ();
        let benchmark_dir = Core.Filename.dirname source_file in
        let meta_config_file =
          Core.Filename.concat benchmark_dir "meta-config.json"
        in
        f source_file meta_config_file)

let prog =
  Command.group ~summary:"Cobb"
    [
      ("synthesis", cobb synthesis_benchmark);
      ("abduction", cobb abduce_benchmark);
      ("config", cobb check_config);
    ]

let () = Command_unix.run prog

(* let () =
   run_benchmark benchmark_to_run.source_file benchmark_to_run.meta_config_file
     benchmark_to_run.bound *)
