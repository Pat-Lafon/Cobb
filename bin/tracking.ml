open Rty
open Language.FrontendTyped
open Utils
open Term
open Mtyped

module NameTracking = struct
  let asts : (identifier, _ typed) Hashtbl.t = Hashtbl.create 128
  let known : (identifier, unit) Hashtbl.t = Hashtbl.create 128

  let debug () =
    print_endline "ASTS";
    Hashtbl.iter
      (fun a b -> Printf.printf "%s -> %s\n" a.x (layout_typed_term b))
      asts;
    print_endline "KNOWN";
    Hashtbl.iter (fun a _ -> Printf.printf "%s\n" a.x) known

  let is_known (name : identifier) = Hashtbl.mem known name

  let known_var (a : identifier) =
    Hashtbl.add known a ();
    Hashtbl.add asts a (a |> id_to_term);
    a

  let add_ast (a : identifier) (term : (t, t term) typed) =
    Hashtbl.add asts a term

  let known_ast (a : identifier) (term : (t, t term) typed) =
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
      | Some ({ x = CVal { x = VConst _; _ }; ty } as t) -> ([], t)
      | Some ({ x = CVal { x = VVar s; _ }; ty } as t) ->
          (* Check for a level of indirection *)
          (* String.equal (layout_typed_term t)
             (aux s |> snd |> layout_typed_term) *)
          if String.equal a.x s.x then ([], t)
          else
            let bindings, rhs = aux s in
            ((a, t) :: bindings, rhs)
      | Some ({ x = CApp { appf; apparg = { x = VVar id; _ } }; ty } as t) ->
          let bindings, rhs = aux id in
          ((a, t) :: bindings, rhs)
      | Some ({ x = CApp { appf; apparg = { x = VConst U; _ } }; ty } as t) ->
          ([ (a, t) ], t)
      | Some { x = CApp { appf; apparg }; ty } ->
          failwith "get_term::unimplemented::CApp"
      | Some ({ x = CAppOp { op; appopargs }; ty } as t) ->
          let args =
            List.map
              (fun x ->
                match x.x with
                | VVar id -> aux id
                | _ -> failwith "get_term::unimplemented::CAppOp")
              appopargs
            |> List.split |> fst |> List.concat
          in
          (args, t)
      | Some { x = CLetE _; _ }
      | Some { x = CLetDeTu _; _ }
      | Some { x = CVal _; _ }
      | Some { x = CErr; _ }
      | Some { x = CMatch _; _ }
      | None ->
          print_endline ("get_term: " ^ a.x);
          Hashtbl.iter
            (fun k v -> k.x ^ " -> " ^ layout_typed_term v |> print_endline)
            asts;
          failwith "get_term"
    in
    let bindings, b = aux a in
    List.fold_left (fun acc (id, rhs) -> mk_lete id rhs acc) b bindings

  let ctx_subst (ctx : t rty Typectx.ctx) (ht : (string, string) Hashtbl.t) :
      t rty Typectx.ctx =
    Typectx.map_ctx_typed
      (fun ({ x; ty } : (t rty, string) typed) : (t rty, string) typed ->
        (* foldLeft ( takes the old type, and the id, substitute if id is in old type, return the new type ) (the unsubstituted type) (the var space ) *)
        let renamed_ty =
          List.fold_left
            (fun t name ->
              if is_known name then t
              else
                let new_name = Hashtbl.find ht name.x in
                subst_rty_instance name.x (AVar new_name #: name.ty) t)
            (* let new_name = Hashtbl.find ht name.x in
               subst_rty_instance name.x (AVar new_name #: (erase_rty t)) t *)
            ty (fv_rty ty)
        in
        let new_name = Hashtbl.find ht x in
        new_name #: renamed_ty)
      ctx

  let freshen (Typectx lst : t rty Typectx.ctx) =
    let ctx = Typectx.Typectx lst in
    let ht : (string, string) Hashtbl.t = Hashtbl.create (List.length lst) in

    let maybe_freshen_one (name_rty : (t rty, string) typed) :
        (t rty, string) typed =
      let name = name_rty #=> erase_rty in
      if is_known name then (
        Hashtbl.add ht name.x name.x;
        name_rty)
      else
        let new_name = (Rename.unique name.x) #: name.ty in
        let () =
          match get_ast name with
          | None -> failwith name.x
          | Some x -> Hashtbl.add asts new_name x
        in
        (* TODO: remove this since context addition checks this already ?*)
        if Hashtbl.mem ht name.x then failwith "duplicate key";
        Hashtbl.add ht name.x new_name.x;
        new_name.x #: name_rty.ty
    in
    let _ = Typectx.map_ctx_typed maybe_freshen_one ctx in

    let res = ctx_subst ctx ht in
    (res, ht)
end
