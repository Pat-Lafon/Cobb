(* underapproximation_type/typecheck *)
open Typecheck

(* underapproximation_type/typecheck/under/underctx.ml *)
open Underctx

(* underapproximation_type/language/languages.ml *)
open Languages

(* underapproximation_type/frontend/underty.ml *)
open Underty.T

(* normalty/src/ast.ml *)
open Normalty.Ast.NT

(* underapproximation_type/autoverificaiton/prop.ml *)
open Autov.Prop

(* underapproximation_type/driver/config.ml *)
open Config
open Assertion
open Sugar
open Languages.StrucNA
open Pieces
open Blocks

type synth_input = {
  name : string;
  source_file : string;
  refine_file : string;
  bound : int;
}

let benchmarks =
  [
    {
      name = "sizedlist";
      source_file =
        "underapproximation_type/data/benchmark/quickchick/sizedlist/prog.ml";
      refine_file =
        "underapproximation_type/data/benchmark/quickchick/sizedlist/_under.ml";
      bound = 1;
    };
    {
      name = "sortedlist";
      source_file =
        "underapproximation_type/data/benchmark/quickchick/sortedlist/prog.ml";
      refine_file =
        "underapproximation_type/data/benchmark/quickchick/sortedlist/_under.ml";
      bound = 3;
    };
    {
      name = "sizedtree";
      source_file =
        "underapproximation_type/data/benchmark/quickchick/sizedtree/prog.ml";
      refine_file =
        "underapproximation_type/data/benchmark/quickchick/sizedtree/_under.ml";
      bound = 3;
    };
    {
      name = "uniquel";
      source_file = "underapproximation_type/data/benchmark/uniquel/prog.ml";
      refine_file = "underapproximation_type/data/benchmark/uniquel/_under.ml";
      bound = 3;
    };
    {
      name = "sizedtree";
      source_file =
        "underapproximation_type/data/benchmark/quickchick/sizedtree/prog.ml";
      refine_file =
        "underapproximation_type/data/benchmark/quickchick/sizedtree/_under.ml";
      bound = 3;
    };
    {
      name = "rbtree";
      source_file =
        "underapproximation_type/data/benchmark/quickchick/rbtree/prog.ml";
      refine_file =
        "underapproximation_type/data/benchmark/quickchick/rbtree/_under.ml";
      bound = 3;
    };
  ]

(* Assumes argument is a fixpoint value *)
let unfold_fix_helper (fix : NL.value) :
    id NNtyped.typed * id NNtyped.typed list * NL.term NNtyped.typed =
  (* Unwrap the function into a recursive call *)
  let[@warning "-8"] (NL.Fix { fixname; fstarg; lambody }) =
    (fix [@warning "+8"])
  in
  (* Handle any other arguments *)
  let rec aux (n : NL.term NNtyped.typed) =
    match n.x with
    | NL.V { x = NL.Lam { lamarg; lambody }; _ } ->
        let other_args, body = aux lambody in
        (lamarg :: other_args, body)
    | _ -> ([], n)
  in
  let other_args, body = aux lambody in
  (fixname, fstarg :: other_args, body)

(* todo can we get rid of the source_file here?*)
let run_benchmark source_file refine_file bound =
  (* This sets up global variables pointing to the information in meta-config.json *)
  let meta_config_file = "meta-config.json" in
  let () = Env.load_meta meta_config_file in
  let () = Config.load_normal () in
  let () = Z3.Params.update_param_value Autov.ctx "timeout" "999" in

  (* prim.ml:init sets up global maps of the stuff that is loaded from the config *)
  let () = Config.load refine_file in

  (*** Notations: ... todo *)
  (*** Libs: a list of library functions loaded in from
    builtin_randomness_coverage_typing: i.e. int_gen, bool_gen, ... *)
  (*** refinements: a list of specifications from the provided `refine_file`
      An option for ...todo
      And a name type pair for the specifications*)
  let notations, libs, refinements =
    Inputstage.load_user_defined_under_refinments refine_file
  in

  (* Check for notations *)
  let _ = assert (List.length notations == 0) in

  (* Check for generator functions *)
  let () = print_string "Import randomness libs: " in
  let _ = List.map (fun (name, x) -> print_string (name ^ ", ")) libs in
  let () = print_newline () in

  (* Check for the program to be synthesized *)
  let _ = assert (List.length refinements == 1) in
  let refinement = List.hd refinements in
  let () = print_endline ("Refinement: " ^ (snd refinement |> fst)) in

  let code = Inputstage.load_ssa libs source_file in

  let nctx =
    Typectx.(
      List.fold_left
        (fun ctx (name, ty) -> add_to_right ctx (name, ty))
        Nctx.empty notations)
  in

  let libctx =
    List.fold_left
      (fun ctx (x, ty) -> Nctx.add_to_right ctx (x, ty))
      Nctx.empty libs
  in

  let seeds, components = Pieces.seeds_and_components libs in

  let opt, (synth_name, synth_type) = refinement in

  (* TODO: not sure what opt is *)
  let () = assert (Option.is_none opt) in

  let { body; name } =
    List.find
      (fun ({ name; _ } : StrucNA.t) -> String.equal name synth_name)
      code
  in

  let () = print_endline ("name : " ^ name) in

  (* term_type_check *)
  let body : NL.value NL.typed =
    match body.x with NL.V x -> x | _ -> failwith "unimplemented"
  in

  let fixname, args, body = unfold_fix_helper body.x in

  (* For other programs that use more than one arg, adjust *)
  let _ = assert (List.length args == 1) in

  let fstarg = List.hd args in

  (* Creating our first argument here *)
  let decreasing_arg : id NNtyped.typed =
    { x = Pieces.known_var (Rename.unique fstarg.x); ty = fstarg.ty }
  in

  (* Unwraps the type signature, basically the first argument is always an overapproximate type(atleast so far)*)
  let[@warning "-8"] (UnderTy_over_arrow { argname; argty; retty }) =
    (synth_type [@warning "+8"])
  in

  let prop =
    Typecheck.Undercheck.make_order_constraint decreasing_arg.x argname
      (snd fstarg.ty)
  in

  print_string "What is prop: ";
  P.to_string prop |> print_endline;

  (* What I believe are some checks about arg types and the synthesis type *)
  let _ =
    Typecheck.Undercheck.erase_check_mk_id __FILE__ __LINE__ decreasing_arg
      (ot_to_ut argty)
  in

  let f =
    Typecheck.Undercheck.erase_check_mk_id __FILE__ __LINE__ fixname synth_type
  in

  let f : id UL.typed =
    {
      x = f.x;
      ty =
        UT.modify_retty
          (fun _ prop' ->
            P.conjunct_tope_uprop __FILE__ __LINE__ [ prop; prop' ])
          f.ty;
    }
  in

  print_endline ("What is decreasing_arg: " ^ decreasing_arg.x);
  print_endline ("What is argname: " ^ argname);

  let ctx' = Typectx.ot_add_to_right Typectx.empty (decreasing_arg.x, argty) in
  let ctx'' =
    Typectx.ut_force_add_to_right ctx' (Pieces.known_var f.x, UtNormal f.ty)
  in

  let args = decreasing_arg :: List.tl args in

  let seeds = List.append seeds (List.map Pieces.mk_var args) in

  (* let () = print_endline "What is in our contexts" in
     let () = print_endline "nctx : " in
     let _ = List.map (fun (x, _) -> print_endline x) nctx in
     let () = print_endline "ctx'' : " in
     let _ = List.map (fun (x, _) -> print_endline x) ctx'' in
     let () = print_endline "libctx : " in
     let _ = List.map (fun (x, _) -> print_endline x) libctx in
     let () = print_newline () in *)
  let retty = UT.subst_id retty argname decreasing_arg.x in

  Blocks.u_type_to_string (ot_to_ut argty) |> print_endline;
  UT.reduce_arrow_type_to_post synth_type
  |> Blocks.u_type_to_string |> print_endline;
  Blocks.u_type_to_string synth_type |> print_endline;
  Blocks.u_type_to_string retty |> print_endline;

  let uctx = { nctx; ctx = ctx''; libctx } in

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

  (* todo Add argument variables to seeds *)

  (* Add Recursive Componenet*)
  let nty = UT.erase f.ty in
  let argtys, resty = NT.destruct_arrow_tp nty in
  let recursive_piece : Pieces.component = Fun { x = f.x; ty = (None, nty) } in
  let components = (recursive_piece, (argtys, resty)) :: components in

  let result = Synthesis.synthesis uctx retty bound seeds components in

  print_endline "Finished Synthesis"

(** Benchmarks can be provided as a command line argument
  * Default is "sizedlist" *)
let benchmark_name =
  if Int.equal (Array.length Sys.argv) 1 then "sizedlist" else Sys.argv.(1)

let benchmark_to_run =
  List.find (fun x -> String.equal x.name benchmark_name) benchmarks

let () =
  run_benchmark benchmark_to_run.source_file benchmark_to_run.refine_file
    benchmark_to_run.bound
