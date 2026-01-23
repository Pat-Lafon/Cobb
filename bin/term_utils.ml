open Term
open Mtyped
open Nt
open Utils
open Cty
open Rty
open Prop
open Language.FrontendTyped

let is_true_prop (phi : Nt.t prop) : bool =
  match phi with
  | Lit { x = AC (Constant.B b); _ } -> b
  | _ -> false

let get_ty_gen_name (base_ty : Nt.t) : identifier =
  let uctx = Context.get_global_uctx () in
  let builtin_list = Typectx.to_list uctx.builtin_ctx in
  let candidates = 
    List.filter_map (fun (entry : (Nt.t rty, string) Mtyped.typed) ->
         match entry.ty with
         | RtyBaseArr { argcty = Cty { nty = Nt.Ty_unit; _ }; retty = RtyBase { cty = Cty { nty; phi }; _ }; _ } 
           when nty = base_ty && is_true_prop phi ->
             Some entry.x
         | _ -> None)
    builtin_list
  in
  match candidates with
  | [gen_name] -> gen_name#:(Ty_arrow (Ty_unit, base_ty))
  | [] -> 
      failwith (Printf.sprintf "No generator found for type %s" (Nt.layout base_ty))
  | _ -> 
      failwith (Printf.sprintf "Multiple generators for type %s: %s" 
        (Nt.layout base_ty) (String.concat ", " candidates))

let term_bot (base_ty : Nt.t) : _ Mtyped.typed = Term.CErr#:base_ty

let term_top (base_ty : Nt.t) : _ Mtyped.typed =
  (*   let ret = (Rename.name ()) #: base_ty in *)
  let unit_value = Constant.U |> constant_to_value in
  (* let unit_name = (Rename.name ()) #: Ty_unit in *)
  let f = get_ty_gen_name base_ty in
  (*  let _, gen_app = Pieces.mk_let_app f unit_name in
  *)
  (*   mk_lete unit_name unit_value gen_app *)
  mk_app (f |> id_to_value) unit_value

let is_base_bot (t : _ Mtyped.typed) : bool =
  match t.x with Term.CErr -> true | _ -> false

(** Keep in Sync with term_top*)
let is_base_top (t : _ Mtyped.typed) : bool =
  match t.x with
  | CLetE
      {
        lhs = _;
        rhs = { x = CVal { x = VVar { x = "TT"; _ }; _ }; _ };
        body = { x = CLetE { body = { x = CVal { x = VVar _; _ }; _ }; _ }; _ };
      } ->
      true
  | CApp { appf = { x = VVar { x = gen_name; _ }; _ }; _ } ->
      let uctx = Context.get_global_uctx () in
      (match Typectx.get_opt uctx.builtin_ctx gen_name with
       | Some (RtyBaseArr { argcty = Cty { nty = Nt.Ty_unit; _ }; retty = RtyBase { cty = Cty { phi; _ }; _ }; _ }) 
         when is_true_prop phi -> 
           true
       | _ -> false)
  | _ -> false
