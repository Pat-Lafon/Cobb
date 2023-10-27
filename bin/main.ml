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

(* This sets up global variables pointing to the information in meta-config.json *)
let () = Env.load_meta meta_config_file

(* prim.ml:init sets up global maps of the stuff that is loaded from the config *)
let () = Config.load refine_file

(*** Notations: ... todo *)
(*** Libs: a list of library functions loaded in from builtin_randomness_coverage_typing because ...todo *)
(*** refinements: a list of specifications from the provided `refine_file`
    An option for ...todo
    And a name type pair for the specifications*)
(* for Inputstage, see underapproximation_type/driver/inputstage.ml *)
let notations, libs, refinements =
  Inputstage.load_user_defined_under_refinments refine_file

let _ = assert (List.length notations == 0)
let dbg_sexp sexp = print_endline (Core.Sexp.to_string_hum sexp)
let dbg (ut : UT.t) = dbg_sexp (UT.sexp_of_t ut)
let () = print_endline (List.length notations |> string_of_int)
let () = print_endline (List.length libs |> string_of_int)

let _ =
  List.map
    (fun (name, x) ->
      print_endline name;
      dbg x)
    libs

let () = print_endline (List.length refinements |> string_of_int)
let _ = List.map (fun (_, (n, _)) -> print_endline n) refinements
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

(* let _ = print_endline "seeds"
   let _ = List.map (fun (name, ty) -> print_endline name) lib_seeds *)

let map_fst f (l, r) = (f l, r)
let map_snd f (l, r) = (l, f r)

let freshen (ctx : Typectx.ctx) =
  let ht = Hashtbl.create (List.length ctx) in
  let add (name : id) =
    let new_name = Rename.unique name in
    (* TODO: remove this since context addition checks this already ?*)
    if Hashtbl.mem ht name then failwith "duplicate key";
    Hashtbl.add ht name new_name;
    new_name
  in
  (List.map (map_fst add) ctx, ht)

let ctx_union_r (l : Typectx.ctx) (r : Typectx.ctx) =
  map_fst (fun res -> l @ res) (freshen r)

(* TODO `ctx_subst` is wrong.
   We need to substitute occurrences of context variables in
   the propositions they appear in. *)
let ctx_subst (ctx : (id * UT.t) list) (ht : (id, id) Hashtbl.t) =
  List.map
    (fun (name, ty) ->
      match Hashtbl.find_opt ht name with
      | Some new_name -> (new_name, UT.subst_id ty name new_name)
      | None -> (name, ty))
    ctx

let seeds, components = Pieces.seeds_and_components libs

(* todo Add argument variables to seeds *)
(* todo Add recursive component *)

(* Example below shows how to build a term and call inference on it *)
let example_term () =
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

  print_endline "Typed int_gen example";
  dbg res;
  dbg_sexp (NL.sexp_of_term prog);
  ()

let _ = example_term ()

(* Asserting that there is only one program to synthesize*)
let () = assert (List.length refinements == 1)
let refinement = List.hd refinements

let result =
  (fun (_, (name', ty)) ->
    match List.find_opt (fun { name; _ } -> String.equal name name') code with
    | None ->
        _failatwith __FILE__ __LINE__
          (spf "The source code of given refinement type '%s' is missing." name')
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

        let () = print_endline "What is in our contexts" in
        let () = print_endline "nctx : " in
        let _ = List.map (fun (x, _) -> print_endline x) nctx in
        let () = print_endline "ctx'' : " in
        let _ = List.map (fun (x, _) -> print_endline x) ctx'' in
        let () = print_endline "libctx : " in
        let _ = List.map (fun (x, _) -> print_endline x) libctx in
        let () = print_newline () in

        let retty = UT.subst_id retty argname decreasing_arg.x in
        let lambody = NL.subst_id (fstarg.x, decreasing_arg.x) lambody in

        dbg retty;
        print_endline "\n\n===\n";

        let seeds =
          List.map
            (fun (x, y) ->
              let name = Rename.name () in
              ( ( name,
                  Trans.to_anormal_with_name name false
                    { x; ty = Some (None, y) } ),
                y ))
            seeds
        in

        let uctx = { nctx; ctx = ctx''; libctx } in

        let seeds =
          List.map
            (fun ((id, term), ty) : (Blocks.block * ty) ->
              let ut = Typecheck.Undercheck.term_type_infer uctx term in
              let seed_utx =
                Typectx.ut_force_add_to_right Typectx.empty (id, UtNormal ut)
              in
              let term_ty = term.ty in
              (({ x = id; ty = term_ty }, ut, seed_utx), ty))
            seeds
        in

        let _ = Synthesis.synthesis uctx retty 2 seeds components in

        let res =
          (* Undersub.type_err_to_false (fun () ->
              Typecheck.Undercheck.term_type_check { nctx; ctx; libctx } body
                ty) *)
          (* Undersub.type_err_to_false (fun () -> *)
          Typecheck.Undercheck.term_type_infer
            { nctx; ctx = ctx''; libctx }
            lambody
        in
        res) (* List.mapi *)
    refinement

let () = dbg result
