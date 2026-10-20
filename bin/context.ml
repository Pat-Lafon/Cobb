open Zutils
open Utils
open Tracking
open Language

let global_bctx : built_in_ctx option ref = ref None

let set_bctx (bctx : built_in_ctx) : unit =
  assert (!global_bctx = None);
  global_bctx := Some bctx

let get_bctx () : built_in_ctx =
  match !global_bctx with
  | Some bctx -> bctx
  | None -> failwith "global bctx not set"

let global_rctx : rctx option ref = ref None

let set_rctx (rctx : rctx) : unit =
  assert (!global_rctx = None);
  global_rctx := Some rctx

let get_rctx () : rctx =
  match !global_rctx with
  | Some rctx -> rctx
  | None -> failwith "global rctx not set"

(* The generator under repair. The enumerator's cost model ranks its recursive
   call and same-return-type components first. *)
let global_goal_func : (string * Nt.t) option ref = ref None
let set_goal_func (v : string * Nt.t) : unit = global_goal_func := Some v
let get_goal_func () : (string * Nt.t) option = !global_goal_func

module LocalCtx = struct
  type t = Nt.t rty Typectx.ctx
  type mapping = (string, identifier) Hashtbl.t

  let cleanup (mapping : mapping) ~(recursive : bool) : unit =
    Hashtbl.to_seq mapping
    |> Seq.filter_map (fun (k, v) -> if k = v.x then None else Some v)
    |> Seq.iter (fun i ->
           if Rename.is_tagged i.x then (
             assert (not (NameTracking.is_known i));
             NameTracking.remove_ast i ~recursive)
           else ())

  let contains_path_cond (ctx : t) : bool =
    List.exists
      (fun { x; _ } -> Core.String.is_prefix ~prefix:path_condition_prefix x)
      (Typectx.ctx_to_list ctx)

  let eq (l : t) (r : t) : bool = Typectx.ctx_to_list l = Typectx.ctx_to_list r

  let layout (ctx : t) : string =
    Typectx.ctx_to_list ctx
    |> List.map (fun { x; ty } -> x ^ " : " ^ layout_rty ty)
    |> String.concat "\n"

  (** [freshen] leaves known names (path conditions, outer vars) untouched, so
      [l] and [r] share them — hence the dedup. *)
  let local_ctx_union_r (l : t) (r : t) : t * mapping =
    map_fst
      (fun res ->
        List.fold_left
          (fun acc x ->
            match Typectx.get_opt acc x.x with
            | Some _ -> acc
            | None -> Typectx.add_to_right acc x)
          l (Typectx.ctx_to_list res))
      (NameTracking.freshen r)

  let extend_rctx (ctx : t) : rctx =
    let rctx = get_rctx () in
    {
      rctx with
      rty_ctx =
        Typectx.ctx_from_list
          (List.concat
             [ Typectx.ctx_to_list rctx.rty_ctx; Typectx.ctx_to_list ctx ]);
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
