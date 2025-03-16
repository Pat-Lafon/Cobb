open Rty
open Language.FrontendTyped
open Utils
open Term
open Mtyped

module NameTracking = struct
  let asts : (identifier, _ typed) Hashtbl.t = Hashtbl.create 12800
  let known : (identifier, unit) Hashtbl.t = Hashtbl.create 128

  let debug () =
    print_endline "ASTS";
    Hashtbl.iter
      (fun a b ->
        Printf.printf "%s ->\n" a.x;
        Utils.dbg_sexp
          (Mtyped.sexp_of_typed Nt.sexp_of_t (Term.sexp_of_term Nt.sexp_of_t) b))
      asts;
    print_endline "KNOWN";
    Hashtbl.iter (fun a _ -> Printf.printf "%s\n" a.x) known

  let is_known (name : identifier) = Hashtbl.mem known name

  let add_ast (a : identifier) (term : (t, t term) typed) =
    assert (not (Hashtbl.mem asts a));
    Hashtbl.replace asts a term

  let rec remove_ast (a : identifier) ~(recursive : bool) =
    assert (Hashtbl.mem asts a);

    (* The problem with removing AST's is that sometimes there are intermediate
       parts that are not removed *)
    if recursive then
      let removed_ast = Hashtbl.find asts a in
      match (removed_ast.x : t term) with
      | CApp { appf = { x = VVar v; _ }; apparg } ->
          if is_known v || not (Hashtbl.mem asts v) then ()
          else remove_ast v ~recursive
      | CAppOp { op; appopargs } -> ()
      | CVal _ -> ()
      | _ -> assert false
    else ();

    (* Actually remove *)
    Hashtbl.remove asts a

  (** Add a variable as known while being duplicate sensative *)
  let known_var (a : identifier) =
    if is_known a then a
    else (
      Hashtbl.replace known a ();
      add_ast a (a |> id_to_term);
      a)

  (** Add an ast as known while being duplicate sensative *)
  let known_ast (a : identifier) (term : (t, t term) typed) =
    assert (not (Hashtbl.mem asts a));
    Hashtbl.add known a ();
    add_ast a term

  let get_ast (a : identifier) = Hashtbl.find_opt asts a

  let ast_to_string ?(erased = false) (id : identifier) : string =
    let term = get_ast id |> Option.get in
    let tterm = if erased then (* Termlang.erase_type  *) term else term in
    layout_typed_term tterm

  let asts_lookup (a : identifier) =
    let expr = get_ast a in
    Option.value expr ~default:(a |> id_to_term)

  let get_term (a : identifier) : (t, t term) typed =
    let rec aux a : _ list * (t, t term) typed =
      let t = get_ast a in
      match t with
      | Some { x = CVal { x = VConst _; _ }; ty } -> failwith "unimplemented"
      | Some ({ x = CVal { x = VVar s; _ }; ty } as t) ->
          (* Check for a level of indirection *)
          (* String.equal (layout_typed_term t)
             (aux s |> snd |> layout_typed_term) *)
          if String.equal a.x s.x then ([], t)
          else
            let bindings, rhs = aux s in
            (bindings, rhs)
      | Some
          ({
             x = CApp { appf = { x = VVar f; _ }; apparg = { x = VVar id; _ } };
             ty;
           } as t) ->
          let bindings, rhs = aux id in
          let bindings =
            if is_known f then
              (* We were provided this function so nothing else needs to be bound *)
              bindings
            else
              (* This is a partial application and we need to get the binding
                 for f *)
              let b, x = aux f in
              bindings @ ((f, x) :: b)
          in
          ((id, rhs) :: bindings, t)
      | Some ({ x = CApp { appf; apparg = { x = VConst U; _ } }; ty } as t) ->
          ([], t)
      | Some { x = CApp { appf; apparg }; ty } ->
          failwith
            ("get_term::unimplemented::CApp : " ^ layout_typed_value appf ^ " "
           ^ layout_typed_value apparg)
      | Some ({ x = CAppOp { op; appopargs }; ty } as t) ->
          let args =
            List.map
              (fun x ->
                match x.x with
                | VVar id -> (
                    let bindings, rhs = aux id in
                    match rhs.x with
                    | CVal { x = VVar v; _ } when v = id -> bindings
                    | _ -> (id, rhs) :: bindings)
                | _ -> failwith "get_term::unimplemented::CAppOp")
              appopargs
            |> List.concat
          in
          (args, t)
      | Some { x = CLetE _; _ }
      | Some { x = CLetDeTu _; _ }
      | Some { x = CVal _; _ }
      | Some { x = CErr; _ }
      | Some { x = CMatch _; _ }
      | None ->
          print_endline ("get_term: " ^ a.x);
          debug ();
          failwith "get_term"
    in
    let bindings, b = aux a in
    List.fold_left
      (fun acc (id, rhs) -> mk_lete id rhs acc)
      b
      (List.rev bindings |> unique)

  let ctx_subst (ctx : t rty Typectx.ctx) (ht : (string, identifier) Hashtbl.t)
      : t rty Typectx.ctx =
    Typectx.map_ctx_typed
      (fun ({ x; ty } : (t rty, string) typed) : (t rty, string) typed ->
        let renamed_ty =
          List.fold_left
            (fun t name ->
              if is_known name then t
              else
                let new_name = Hashtbl.find ht name.x in
                assert (new_name.ty = name.ty);
                subst_rty_instance name.x (AVar new_name) t)
            ty (fv_rty ty)
        in
        let new_name = Hashtbl.find ht x in
        assert (new_name.ty = Rty.erase_rty renamed_ty);
        new_name.x#:renamed_ty)
      ctx

  let rename (id : identifier) : identifier =
    (* if is_known id then id
    else *)
      let new_name = (Rename.unique id.x)#:id.ty in
      assert (not (Hashtbl.mem asts new_name));
      let () =
        match get_ast id with
        | None -> failwith id.x
        | Some x -> add_ast new_name x
      in
      new_name

  let freshen (Typectx lst : t rty Typectx.ctx) =
    let ctx = Typectx.Typectx lst in
    let ht : (string, identifier) Hashtbl.t =
      Hashtbl.create (List.length lst)
    in

    let maybe_freshen_one (name_rty : (t rty, string) typed) :
        (t rty, string) typed =
      let name = name_rty#=>erase_rty in
      if is_known name then (
        Hashtbl.replace ht name.x name;
        name_rty)
      else
        let new_name = (Rename.unique name.x)#:name.ty in
        let () =
          match get_ast name with
          | None -> failwith name.x
          | Some x -> add_ast new_name x
        in
        assert (not (Hashtbl.mem ht name.x));
        Hashtbl.replace ht name.x new_name;
        new_name.x#:name_rty.ty
    in
    let _ = Typectx.map_ctx_typed maybe_freshen_one ctx in

    let res = ctx_subst ctx ht in
    (res, ht)

  (* TODO: I use a string here because I don't want to create a cycle between
    tracking and Pieces *)
  let rec term_contains_component (a : identifier) (c : string) : bool =
    match Hashtbl.find_opt asts a with
    | None -> false
    | Some x -> (
        match x.x with
        | CVal { x = VVar v; _ } ->
            if not (String.equal v.x a.x) then (
              print_endline "hit";
              term_contains_component v c)
            else false
        | CApp { appf = { x = VVar f; _ }; apparg } -> (
            String.equal f.x c
            ||
            match apparg.x with
            | VConst _ -> false
            | VVar v -> term_contains_component v c
            | _ ->
                print_endline (layout_typed_value apparg);
                failwith "I don't think I should hit that?")
        | CAppOp { op; appopargs } ->
            Op.op_name_for_typectx op.x |> String.equal c
            || List.exists
                 (fun x ->
                   match x.x with
                   | VVar v -> term_contains_component v c
                   | _ -> failwith "I don't think I should hit this")
                 appopargs
        | _ -> failwith "I don't think")
end
