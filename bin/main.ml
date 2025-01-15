open Pieces
open Blocks
open Blockmap
open Block
open Localization
open Language.FrontendTyped
open Zzdatatype.Datatype
open Mtyped
open Synthesiscollection
open Preprocess
open Postprocess
module Env = Zzenv

type config = {
  bound : int;
  res_ext : string;
  abd_ext : string;
  syn_ext : string;
  syn_rlimit : int;
  abd_rlimit : int;
  type_rlimit : int;
  use_missing_coverage_file : bool;
  collect_ext : string;
  component_list : string list;
}

type benchmark_results = {
  synth_result : bool option;
  bound : int option;
  num_localized_paths : int option;
  resource_limit : int option;
  queries : int option;
  abd_time : float option;
  synth_time : float option;
  total_time : float option;
}

let new_benchmark_results () =
  {
    synth_result = None;
    bound = None;
    num_localized_paths = None;
    resource_limit = None;
    queries = None;
    abd_time = None;
    synth_time = None;
    total_time = None;
  }

let write_results_to_file results_file results =
  let default_str to_str x = Option.fold x ~some:to_str ~none:"" in

  let results_csv_contents =
    Printf.sprintf
      "Result, Bounds, Resource Limit, Queries, Abd Time, Synth Time, Total Time\n\
       %s, %s, %s, %s, %s, %s, %s"
      (default_str string_of_bool results.synth_result)
      (default_str string_of_int results.bound)
      (default_str string_of_int results.resource_limit)
      (default_str string_of_int results.queries)
      (default_str (Printf.sprintf "%.2f") results.abd_time)
      (default_str (Printf.sprintf "%.2f") results.synth_time)
      (default_str (Printf.sprintf "%.2f") results.total_time)
  in
  Core.Out_channel.write_all results_file ~data:results_csv_contents

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
  let type_rlimit = metaj |> member "type_rlimit" |> to_int in
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
    type_rlimit;
    collect_ext;
    component_list;
    use_missing_coverage_file;
  }

let set_z3_rlimit rlimit =
  Z3.Params.update_param_value Backend.Smtquery.ctx "rlimit"
    (string_of_int rlimit)

let check_config _ meta_config_file =
  let _ = get_synth_config_values meta_config_file in
  ()

let abduce_or_provide_missing (config : config) (source_file : string)
    (meta_config_file : string) (start_time : float) : t Rty.rty * float =
  let missing_coverage, abd_time =
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

      (unfold_rty_helper missing_rty |> snd, 0.0))
    else (
      set_z3_rlimit config.abd_rlimit;

      let missing_coverage =
        Commands.Cre.type_infer_inner meta_config_file source_file ()
      in
      let abd_time = Sys.time () -. start_time in
      (missing_coverage, abd_time))
  in
  (missing_coverage, abd_time)

let abduce_benchmark source_file meta_config_file =
  let config = get_synth_config_values meta_config_file in

  set_z3_rlimit config.abd_rlimit;

  let start_time = Sys.time () in

  (* let missing_coverage =
       Commands.Cre.type_infer_inner meta_config_file source_file ()
     in

     let abd_time = Sys.time () -. start_time in
  *)
  let missing_coverage, abd_time =
    abduce_or_provide_missing config source_file meta_config_file start_time
  in

  let abduction_file = source_file ^ config.abd_ext in

  let results_file = source_file ^ config.res_ext ^ ".csv" in

  let results = new_benchmark_results () in
  let results = { results with queries = Some !Backend.Check.query_counter } in
  let results = { results with abd_time = Some abd_time } in

  let () =
    if Sys_unix.is_file_exn abduction_file then
      let previous_coverage = Core.In_channel.read_all abduction_file in
      let current_coverage = layout_rty missing_coverage in
      assert (String.equal previous_coverage current_coverage)
    else
      Core.Out_channel.write_all abduction_file
        ~data:(layout_rty missing_coverage)
  in
  write_results_to_file results_file results

let localize_benchmark source_file meta_config_file =
  let config = get_synth_config_values meta_config_file in

  set_z3_rlimit config.abd_rlimit;

  let start_time = Sys.time () in

  (* let missing_coverage =
       Commands.Cre.type_infer_inner meta_config_file source_file ()
     in *)
  let missing_coverage, abd_time =
    abduce_or_provide_missing config source_file meta_config_file start_time
  in

  set_z3_rlimit config.syn_rlimit;

  let uctx = build_initial_typing_context () in

  let args, rec_fix, retty, body, reconstruct_code_with_new_body =
    get_args_rec_retty_body_from_source source_file
  in

  let uctx = add_to_rights uctx (rec_fix :: args) in

  Context.set_global_uctx uctx;

  let path_maps, new_body =
    Localization.localization uctx body missing_coverage
  in

  let num_localized_paths = List.length path_maps in
  Printf.printf "Number of paths: %d\n" num_localized_paths

let synthesis_benchmark source_file meta_config_file =
  let config = get_synth_config_values meta_config_file in

  let start_time = Sys.time () in

  (* let missing_coverage, abd_time =
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

         (unfold_rty_helper missing_rty |> snd, 0.0))
       else (
         set_z3_rlimit config.abd_rlimit;

         let missing_coverage =
           Commands.Cre.type_infer_inner meta_config_file source_file ()
         in
         let abd_time = Sys.time () -. start_time in
         (missing_coverage, abd_time))
     in *)
  let missing_coverage, abd_time =
    abduce_or_provide_missing config source_file meta_config_file start_time
  in

  print_endline ("Components" ^ String.concat "," config.component_list);

  Printf.printf "Missing Coverage: %s\n" (layout_rty missing_coverage);

  if Utils.rty_is_false missing_coverage then failwith "No missing coverage";

  set_z3_rlimit config.type_rlimit;

  let synth_start_time = Sys.time () in

  let collection_file = source_file ^ config.collect_ext in

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
  set_z3_rlimit config.syn_rlimit;

  assert (Typing.Termcheck.term_type_infer uctx body |> Option.is_some);

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

  let num_localized_paths = List.length path_maps in

  print_endline ("Number of paths: " ^ string_of_int num_localized_paths);

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

  (* print_endline "Initial collection";
     SynthesisCollection.print init_synth_col; *)
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
    |> remove_excess_ast_aux |> remove_underscores_in_variable_names_typed
  in

  print_endline ("New_body :\n" ^ layout_typed_term new_body);

  (*   print_endline ("Return Type: \n" ^ layout_rty retty); *)
  let synth_time = Sys.time () -. synth_start_time in

  set_z3_rlimit config.type_rlimit;

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

  let results = new_benchmark_results () in
  let results = { results with synth_result = Some result } in
  let results = { results with bound = Some config.bound } in
  let results =
    { results with num_localized_paths = Some num_localized_paths }
  in
  let results = { results with resource_limit = Some config.syn_rlimit } in
  let results = { results with queries = Some !Backend.Check.query_counter } in
  let results = { results with abd_time = Some abd_time } in
  let results = { results with synth_time = Some synth_time } in
  let results = { results with total_time = Some total_time } in

  write_results_to_file results_file results;

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
      ("localize", cobb localize_benchmark);
    ]

let () = Command_unix.run prog
