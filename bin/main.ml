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

(* todo can we get rid of the source_file here?*)
let run_benchmark source_file refine_file bound =
  (* This sets up global variables pointing to the information in meta-config.json *)
  let meta_config_file = "meta-config.json" in
  let () = Env.load_meta meta_config_file in

  (* prim.ml:init sets up global maps of the stuff that is loaded from the config *)
  let () = Config.load refine_file in

  (*** Notations: ... todo *)
  (*** Libs: a list of library functions loaded in from builtin_randomness_coverage_typing because ...todo *)
  (*** refinements: a list of specifications from the provided `refine_file`
      An option for ...todo
      And a name type pair for the specifications*)
  (* for Inputstage, see underapproximation_type/driver/inputstage.ml *)
  let notations, libs, refinements =
    Inputstage.load_user_defined_under_refinments refine_file
  in

  let _ = assert (List.length notations == 0) in
  let dbg_sexp sexp = print_endline (Core.Sexp.to_string_hum sexp) in
  let dbg (ut : UT.t) = dbg_sexp (UT.sexp_of_t ut) in

  (* let () = print_endline (List.length notations |> string_of_int) in *)
  (*   let () = print_endline (List.length libs |> string_of_int) in *)

  (* let _ =
     List.map
       (fun (name, x) ->
         print_endline name;
         dbg x)
       libs *)

  (* let () = print_endline (List.length refinements |> string_of_int) in *)
  let _ = List.map (fun (_, (n, _)) -> print_endline n) refinements in
  let code = Inputstage.load_ssa libs source_file in

  let nctx =
    Typectx.(
      List.fold_left
        (fun ctx (name, ty) -> add_to_right ctx (name, ty))
        empty notations)
  in

  let libctx =
    List.fold_left
      (fun ctx (x, ty) -> Nctx.add_to_right ctx (x, ty))
      Nctx.empty libs
  in

  let seeds, components = Pieces.seeds_and_components libs in

  (* todo Add argument variables to seeds *)
  (* todo Add recursive component *)

  (* Example below shows how to build a term and call inference on it *)
  (* let example_term () =
       let int_gen = List.nth libs 2 in

       let t_int_gen : id NL.typed =
         { x = fst int_gen; ty = (None, Underty.T.erase (snd int_gen)) }
       in

       let four = NL.V { x = NL.Lit (NL.ConstI 4); ty = (None, Ty_int) } in
       let _, prog =
         Pieces.mk_ctor
           { x = "tt"; ty = (None, Ty_unit) }
           []
           (fun v ->
             {
               x =
                 Pieces.mk_app t_int_gen [ v ] (fun v ->
                     NL.value_to_term (NL.id_to_value v))
                 |> snd;
               ty = (None, Ty_int);
             })
       in
       let res =
         Typecheck.Undercheck.term_type_infer
           { nctx; ctx = Typectx.empty; libctx }
           { x = prog; ty = (None, Ty_int) }
       in
     (*
       print_endline "Typed int_gen example";
       dbg res;
       dbg_sexp (NL.sexp_of_term prog); *)
       ()

     let _ = example_term () *)

  (* Asserting that there is only one program to synthesize*)
  let () = assert (List.length refinements == 1) in
  let refinement = List.hd refinements in

  let result =
    (fun (_, (name', ty)) ->
      match
        List.find_opt
          (fun ({ name; _ } : StrucNA.t) -> String.equal name name')
          code
      with
      | None ->
          _failatwith __FILE__ __LINE__
            (spf "The source code of given refinement type '%s' is missing."
               name')
      | Some { body; name } ->
          print_string "name : ";
          print_endline name;
          (* term_type_check *)
          let body : NL.term NL.typed = body in

          let body : NL.value NL.typed =
            match body.x with NL.V x -> x | _ -> failwith "unimplemented"
          in

          (* passing off to value_type_check *)

          (* Unwrap the function into a recursive call *)
          let[@warning "-8"] (NL.Fix { fixname; fstarg; lambody }) =
            (body.NL.x [@warning "+8"])
          in
          (* and unwrap the type signature *)
          let[@warning "-8"] (UnderTy_over_arrow { argname; argty; retty }) =
            (ty [@warning "+8"])
          in

          let decreasing_arg =
            NL.{ x = Pieces.known_var (Rename.unique fstarg.x); ty = fstarg.ty }
          in
          let prop =
            Typecheck.Undercheck.make_order_constraint decreasing_arg.x argname
              (snd fstarg.ty)
          in

          print_string "What is prop: ";
          P.to_string prop |> print_endline;

          let _ =
            Typecheck.Undercheck.erase_check_mk_id __FILE__ __LINE__
              decreasing_arg (ot_to_ut argty)
          in

          let f =
            Typecheck.Undercheck.erase_check_mk_id __FILE__ __LINE__ fixname ty
          in
          let f =
            UL.
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

          let ctx' =
            Typectx.ot_add_to_right Typectx.empty (decreasing_arg.x, argty)
          in
          let ctx'' =
            Typectx.ut_force_add_to_right ctx'
              (Pieces.known_var f.x, UtNormal f.ty)
          in

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
          UT.reduce_arrow_type_to_post ty
          |> Blocks.u_type_to_string |> print_endline;
          Blocks.u_type_to_string ty |> print_endline;
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

          (* Add arguments as variables *)

          (* Add Recursive Componenet*)
          let nty = UT.erase f.ty in
          let argtys, resty = NT.destruct_arrow_tp nty in
          let recursive_piece : Pieces.component =
            Fun { x = f.x; ty = (None, nty) }
          in
          let components = (recursive_piece, (argtys, resty)) :: components in

          Synthesis.synthesis uctx retty bound seeds components
      (*
          let res =
            (* Undersub.type_err_to_false (fun () ->
                Typecheck.Undercheck.term_type_check { nctx; ctx; libctx } body
                  ty) *)
            (* Undersub.type_err_to_false (fun () -> *)
            Typecheck.Undercheck.term_type_infer
              { nctx; ctx = ctx''; libctx }
              lambody
          in
          res *))
      (* List.mapi *)
      refinement
  in
  print_endline "Finished Synthesis"

(** Benchmarks can be provided as a command line argument *)
let benchmark_name =
  if Int.equal (Array.length Sys.argv) 1 then "sizedlist" else Sys.argv.(1)

let benchmark_to_run =
  List.find (fun x -> String.equal x.name benchmark_name) benchmarks

let () =
  run_benchmark benchmark_to_run.source_file benchmark_to_run.refine_file
    benchmark_to_run.bound
