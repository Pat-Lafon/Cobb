open Typing
open Mtyped
open Rty
open Cty
open Term
open Tracking
open Language.FrontendTyped
open Zzdatatype.Datatype
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

let rec strip_lam (t : (_, _ term) typed) : (_, _ term) typed =
  match t.x with
  | CVal { x = VLam { lamarg; body }; _ } -> strip_lam body
  | _ -> t

(* Largely taken straight from value_type_check::VFix *)
let handle_recursion_args (a : (Nt.t, Nt.t value) typed) (rty : Nt.t rty) =
  assert (Nt.eq a.ty (Rty.erase_rty rty));
  match (a.x, rty) with
  | VFix { fixname; fixarg; body }, RtyBaseArr { argcty; arg; retty } ->
      assert (String.equal fixarg.x arg);

      let ret_nt_ty = Nt.destruct_arr_tp fixname.ty |> snd in

      if String.equal "stlc_term" (ret_nt_ty |> Nt.layout) then
        match (body.x, retty) with
        | ( CVal { x = VLam { lamarg; body }; _ },
            RtyBaseArr { argcty = argcty1; arg = arg1; retty } ) ->
            let rty' =
              let arg' = { x = Rename.unique arg; ty = fixarg.ty } in
              let arg = arg #: fixarg.ty in
              let arg1' = { x = Rename.unique arg1; ty = lamarg.ty } in
              let arg1 = arg1 #: lamarg.ty in
              let rec_constraint_cty = Termcheck.apply_rec_arg2 arg arg' arg1 in
              let () =
                Termcheck.init_cur_rec_func_name
                  (fixname.x, rec_constraint_cty, ret_nt_ty)
              in
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
          Termcheck.init_cur_rec_func_name
            (fixname.x, rec_constraint_cty, ret_nt_ty)
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
