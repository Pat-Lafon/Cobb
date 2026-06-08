open Zutils
open Language
open Utils

let is_true_prop (phi : Nt.t prop) : bool =
  match phi with
  | Lit { x = AC (B b); _ } -> b
  | _ -> false

let get_ty_gen_name (base_ty : Nt.t) : identifier =
  let builtin_list = Typectx.ctx_to_list (Context.get_bctx ()).builtin_ctx in
  let candidates =
    List.filter_map (fun (entry : (Nt.t rty, string) typed) ->
         match entry.ty with
         | RtyArr { argrty = RtyBase { cty = { nty = Nt.Ty_constructor ("unit", []); _ }; _ };
                    retty = RtyBase { cty = { nty; phi }; _ }; _ }
           when nty = base_ty && is_true_prop phi ->
             Some entry.x
         | _ -> None)
    builtin_list
  in
  match candidates with
  | [gen_name] -> gen_name#:(Nt.Ty_arrow (Nt.unit_ty, base_ty))
  | [] ->
      failwith (Printf.sprintf "No generator found for type %s" (Nt.layout base_ty))
  | _ ->
      failwith (Printf.sprintf "Multiple generators for type %s: %s"
        (Nt.layout base_ty) (String.concat ", " candidates))

let term_bot (base_ty : Nt.t) : _ typed = CErr#:base_ty

let term_top (base_ty : Nt.t) : _ typed =
  (*   let ret = (Rename.fresh_var ()) #: base_ty in *)
  let unit_value = U |> constant_to_value in
  (* let unit_name = (Rename.fresh_var ()) #: Ty_unit in *)
  let f = get_ty_gen_name base_ty in
  (*  let _, gen_app = Pieces.mk_let_app f unit_name in
  *)
  (*   mk_lete unit_name unit_value gen_app *)
  mk_app (f |> id_to_value) unit_value

let is_base_bot (t : _ typed) : bool =
  match t.x with CErr -> true | _ -> false

(** Keep in Sync with term_top*)
let is_base_top (t : _ typed) : bool =
  match t.x with
  | CLetE
      {
        lhs = _;
        rhs = { x = CVal { x = VVar { x = "TT"; _ }; _ }; _ };
        body = { x = CLetE { body = { x = CVal { x = VVar _; _ }; _ }; _ }; _ };
      } ->
      true
  | CApp { appf = { x = VVar { x = gen_name; _ }; _ }; _ } ->
      (match Typectx.get_opt (Context.get_bctx ()).builtin_ctx gen_name with
       | Some (RtyArr { argrty = RtyBase { cty = { nty = Nt.Ty_constructor ("unit", []); _ }; _ };
                        retty = RtyBase { cty = { phi; _ }; _ }; _ })
         when is_true_prop phi ->
           true
       | _ -> false)
  | _ -> false
