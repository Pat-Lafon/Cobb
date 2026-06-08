open Zutils
open Utils
open Tracking
open Language
open Typing.Termcheck

type nonrec uctx = uctx = { bctx : built_in_ctx; rctx : rctx }

(** There is only one global, uctx for the synthesis problem *)
let global_uctx : uctx option ref = ref None

let set_global_uctx (uctx : uctx) : unit =
  assert (!global_uctx = None);
  global_uctx := Some uctx

let get_global_uctx () : uctx =
  match !global_uctx with
  | Some uctx -> uctx
  | None -> failwith "global uctx not set"

let get_bctx () : built_in_ctx = (get_global_uctx ()).bctx

module LocalCtx = struct
  type t = Nt.t rty Typectx.ctx
  type mapping = (string, identifier) Hashtbl.t

  let cleanup (mapping : mapping) ~(recursive : bool) : unit =
    Hashtbl.to_seq mapping
    |> Seq.filter_map (fun (k, v) -> if k = v.x then None else Some v)
    |> Seq.iter (fun i ->
           let _, suffix = Rename.name_of_string i.x in
           if Option.is_some suffix then (
             assert (not (NameTracking.is_known i));
             NameTracking.remove_ast i ~recursive)
           else ())

  let contains_path_cond (ctx : t) : bool =
    List.exists
      (fun { x; _ } -> Core.String.is_prefix ~prefix:path_condition_prefix x)
      (Typectx.ctx_to_list ctx)

  let eq (l : t) (r : t) : bool =
    Typectx.ctx_to_list l = Typectx.ctx_to_list r

  let layout (ctx : t) : string =
    Typectx.ctx_to_list ctx
    |> List.map (fun { x; ty } -> x ^ " : " ^ layout_rty ty)
    |> String.concat "\n"

  (** Combining to local contexts together with renaming *)
  let local_ctx_union_r (l : t) (r : t) : t * mapping =
    let l_list = Typectx.ctx_to_list l in
    map_fst
      (fun res -> Typectx.ctx_from_list (l_list @ Typectx.ctx_to_list res))
      (NameTracking.freshen r)

  (** Carefully adds the local context to uctx * You should probably use this
      for constructing uctx's *)
  let uctx_add_local_ctx (ctx : t) : uctx =
    let uctx = get_global_uctx () in
    {
      uctx with
      rctx =
        {
          uctx.rctx with
          rty_ctx =
            Typectx.ctx_from_list
              (List.concat
                 [
                   Typectx.ctx_to_list ctx;
                   Typectx.ctx_to_list uctx.rctx.rty_ctx;
                 ]);
        };
    }

  (** Take a local context and add the local context of a path which should have
      only path constraints and local vars. must not be incompatible contexts *)
  let promote_ctx_to_path (local_ctx : t) ~promote_ctx =
    let local_ctx = Typectx.ctx_to_list local_ctx in
    let promote_ctx = Typectx.ctx_to_list promote_ctx in
    assert (
      List.for_all
        (fun { x; _ } -> List.for_all (fun { x = x'; _ } -> x' <> x) local_ctx)
        promote_ctx);

    Typectx.ctx_from_list (local_ctx @ promote_ctx)

  let exists_rtys_to_rty (ctx : t) rty =
    Auxtyping.exists_rtys (Typectx.ctx_to_list ctx) rty

  (* Only allowed when the old_name is not used in any other types *)
  let update_name (ctx : t) old_name new_name =
    Typectx.ctx_to_list ctx
    |> List.map (fun { x; ty } ->
           (* Assert that the old name is not a free variable in any type *)
           assert (not (List.mem old_name (fv_rty_id ty)));
           if x = old_name then { x = new_name; ty } else { x; ty })
    |> Typectx.ctx_from_list

  let remove_duplicates (ctx : t) : t =
    let empty = Typectx.emp in

    let new_locals =
      List.fold_left
        (fun acc x ->
          match Typectx.get_opt acc x.x with
          | None -> Typectx.add_to_right acc x
          | Some _ -> acc)
        empty (Typectx.ctx_to_list ctx)
    in

    new_locals
end
