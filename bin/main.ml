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

let todo () = failwith "unimplemented"

(*

(* All of the basenames come as some string ID... not sure where from*)
let my_basename = "v1"
(* The base version of the type*)
let my_normalty = Ty_arrow (Ty_int, Ty_int)
(* The predicate attached to the base type*)
let my_prop = Lit (ACbool true)

(* This is some kind of list of (String, Underapproximate Types from ast/underty.ml)*)
let my_libctx = [("Inc", UnderTy_base {basename = my_basename; normalty = my_normalty; prop = my_prop})]

(*
  I'm not 100% on what it contains but it looks like a context, a normalized context, and a library context
*)
let under_ctx = {
  ctx = [];
  nctx = [];
  libctx = my_libctx;
}

(* Some normalized term in the language which has a type that doesn't make much sense to me*)
let term = Languages.NL.V ({x=(Lit (ConstI 1)); ty= None, Ty_int})
let typed_term: NL.term NNtyped.typed = {x = term; ty = None, Ty_int}

(* This is our main inference worker *)
(* It takes an underapproximate context and a normalized term and produces that terms underapproximate type*)
let x = Typecheck.Undercheck.term_type_infer under_ctx typed_term

let () = print_endline "Hello, World!"


 *)

(** As if we are setting this up from main *)
let meta_config_file = "meta-config.json"

let source_file =
  "underapproximation_type/data/benchmark/quickchick/sizedlist/prog.ml"

let refine_file =
  "underapproximation_type/data/benchmark/quickchick/sizedlist/_under.ml"

let () = Env.load_meta meta_config_file
let () = Config.load refine_file

let notations, libs, refinements =
  Inputstage.load_user_defined_under_refinments refine_file

let code = Inputstage.load_ssa libs source_file

let nctx =
  Typectx.(
    List.fold_left
      (fun ctx (name, ty) -> add_to_right ctx (name, ty))
      empty notations)

let libctx =
  List.fold_left
    (fun ctx (x, ty) -> Nctx.add_to_right ctx (x, ty))
    Nctx.empty libs

let results =
  List.mapi
    (fun _ (_, (name', ty)) ->
      match List.find_opt (fun { name; _ } -> String.equal name name') code with
      | None ->
          _failatwith __FILE__ __LINE__
            (spf "The source code of given refinement type '%s' is missing."
               name')
      | Some { body; name } ->
          (* term_type_check *)
          let body : NL.term NL.typed = body in

          let body : NL.value NL.typed =
            match body.x with NL.V x -> x | _ -> todo ()
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
            NL.{ x = Rename.unique fstarg.x; ty = fstarg.ty }
          in
          let prop =
            Typecheck.Undercheck.make_order_constraint decreasing_arg.x argname
              (snd fstarg.ty)
          in
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
          let ctx' =
            Typectx.ot_add_to_right Typectx.empty (decreasing_arg.x, argty)
          in
          let ctx'' = Typectx.ut_force_add_to_right ctx' (f.x, UtNormal f.ty) in
          let retty = UT.subst_id retty argname decreasing_arg.x in
          let lambody = NL.subst_id (fstarg.x, decreasing_arg.x) lambody in

          let formatter = Format.formatter_of_out_channel Out_channel.stdout in
          let () = Core.Sexp.pp_hum formatter (UT.sexp_of_t retty) in
          let () = Format.pp_print_flush formatter () in

          print_endline "\n\n===\n";

          let res =
            (* Undersub.type_err_to_false (fun () ->
                Typecheck.Undercheck.term_type_check { nctx; ctx; libctx } body
                  ty) *)
            (* Undersub.type_err_to_false (fun () -> *)
            Typecheck.Undercheck.term_type_infer
              { nctx; ctx = ctx''; libctx }
              lambody
          in
          res)
    refinements

(* let () = List.iter (fun x -> print_endline (string_of_bool x)) results *)

let results = List.map UT.sexp_of_t results
let formatter = Format.formatter_of_out_channel Out_channel.stdout
let () = List.iter (Core.Sexp.pp_hum formatter) results
let () = Format.pp_print_flush formatter ()
