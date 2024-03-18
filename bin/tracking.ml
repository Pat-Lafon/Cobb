open Rty
open Language.FrontendTyped
open Utils
open Term
open Mtyped

module NameTracking = struct
  let asts : (identifier, _ typed) Hashtbl.t = Hashtbl.create 128
  let known : (identifier, unit) Hashtbl.t = Hashtbl.create 128
  let is_known (name : identifier) = Hashtbl.mem known name

  let known_var (a : identifier) =
    Hashtbl.add known a ();
    Hashtbl.add asts a (a |> id_to_term);
    a

  let add_ast (a : identifier) (term : (t, t term) typed) =
    Hashtbl.add asts a term

  let get_ast (a : identifier) = Hashtbl.find_opt asts a

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
                subst_rty_instance name.x (AVar new_name #: (erase_rty t)) t)
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
          match Hashtbl.find_opt asts name with
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
