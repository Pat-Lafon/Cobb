open Zutils
open Zdatatype
open Language
open Auxtyping
open Tracking

let rec unfold_rty_helper rty : _ typed list * _ rty =
  match rty with
  (* | RtyArrArr { argrty : 't rty; retty : 't rty } ->
      let other_args, retty = unfold_rty_helper retty in
      (argrty :: other_args, retty) *)
  | RtyArr { argrty = RtyBase { cty = argcty; _ }; arg; retty } ->
      let other_args, retty = unfold_rty_helper retty in
      ((arg#:(RtyBase { ou = Over; cty = argcty })) :: other_args, retty)
  | RtyBase _ -> ([], rty)
  | _ -> failwith "unfold_rty_helper::error"

let rec strip_lam (t : (_, _ term) typed) : (_, _ term) typed =
  match t.x with
  | CVal { x = VLam { lamarg; body }; _ } -> strip_lam body
  | _ -> t

(* Largely taken straight from value_type_check::VFix *)
let handle_recursion_args (a : (Nt.t, Nt.t value) typed) (rty : Nt.t rty) =
  assert (Nt.equal_nt a.ty (erase_rty rty));
  match (a.x, rty) with
  | ( VFix { fixname; fixarg; body },
      RtyArr { argrty = RtyBase { cty = argcty; _ }; arg; retty } ) ->
      assert (String.equal fixarg.x arg);

      let ret_nt_ty = Nt.destruct_arr_tp fixname.ty |> snd in

      let retty = subst_rty_instance arg (AVar fixarg) retty in

      let rec_constraint_cty =
        { nty = fixarg.ty; phi = mk_self_wf_dec fixarg }
      in
      let () = Context.set_goal_func (fixname.x, ret_nt_ty) in
      let rty' =
        let a = { x = Rename.unique fixarg.x; ty = fixarg.ty } in
        RtyArr
          {
            argrty =
              RtyBase
                {
                  ou = Over;
                  cty = n_to_one_ctys smart_and [ argcty; rec_constraint_cty ];
                };
            arg = a.x;
            retty =
              subst_rty_instance arg (AVar (NameTracking.known_var a)) retty;
          }
      in
      (*       Pp.printf "\nSubstituted Return Type: %s\n" (layout_rty retty_a); *)
      (*       Pp.printf "\nRty A: %s\n" (layout_rty rty_a); *)
      (*       Pp.printf "\nRty A: %s\n" (layout_rty rty_a); *)
      let binding = fixarg.x#:(RtyBase { ou = Over; cty = argcty }) in
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
          (sexp_of_rty Nt.sexp_of_nt _retty)
          (sexp_of_rty Nt.sexp_of_nt retty));
      let rec_fix = fixname.x#:rty' in

      ([ binding ], rec_fix, rec_constraint_cty, strip_lam body)
  | _ -> failwith "Did not recieve a fixpoint value and a base arrow type"

let init_typing_context () : rctx =
  Context.set_bctx (Preprocess.load_bctx ());
  Typing.Rctx.emp "synth" [] []

let rec swap_in_body (code : (Nt.t, Nt.t value) typed) :
    (Nt.t, Nt.t term) typed -> (Nt.t, Nt.t value) typed =
  match code.x with
  | VFix { fixname; fixarg; body = { x = CVal body; ty } } ->
      fun x ->
        let b : _ -> (Nt.t, Nt.t value) typed = swap_in_body body in
        (VFix { fixname; fixarg; body = b x |> value_to_term })#:code.ty
  | VFix { fixname; fixarg; body } -> (
      fun x : (Nt.t, Nt.t value) typed ->
        (VFix { fixname; fixarg; body = x })#:code.ty)
  | VLam { lamarg; body = { x = CVal body; ty } } ->
      fun x ->
        let b : _ -> (Nt.t, Nt.t value) typed = swap_in_body body in
        (VLam { lamarg; body = b x |> value_to_term })#:code.ty
  | VLam { lamarg; body } -> (
      fun x : (Nt.t, Nt.t value) typed -> (VLam { lamarg; body = x })#:code.ty)
  | _ -> failwith "swap_in_body::failure"

let get_args_rec_retty_body_from_source source_file =
  let processed_file = Preprocess.preprocess [ source_file ] in

  assert (List.length processed_file = 2);

  (*  Pp.printf "\nProcessed File:\n%s\n" (layout_structure processed_file); *)
  let synth_name, synth_type =
    List.find_map
      (fun item ->
        match item with
        | MRty { name; is_assumption; rty } ->
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
        | MFuncImp { name = { x; _ }; if_rec = true; body }
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
    MFuncImp
      {
        name = synth_name#:(erase_rty synth_type);
        if_rec = true;
        body = b x |> value_to_term;
      }
  in

  let first_arg, rec_fix, rec_bound, body =
    handle_recursion_args code synth_type
  in
  (* Pp.printf "Body: %s\n" (layout_typed_term body);
     List.iter (fun x -> Pp.printf "\nArg: %s\n" (layout_id_rty x)) first_arg;
     Pp.printf "\nRec Fix: %s\n" (layout_id_rty rec_fix); *)
  let args =
    first_arg
    @ List.sublist argtyps ~start_included:(List.length first_arg)
        ~end_excluded:(List.length argtyps)
  in
  (args, rec_fix, rec_bound, retty, body, reconstruct_code_with_new_body)
