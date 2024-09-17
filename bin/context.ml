open Language.FrontendTyped
open Utils
open Tracking
open Language

(** There is only one global, uctx for the synthesis problem *)
let global_uctx : uctx option ref = ref None

let set_global_uctx (uctx : uctx) : unit =
  assert (!global_uctx = None);
  global_uctx := Some uctx

let get_global_uctx () : uctx =
  match !global_uctx with
  | Some uctx -> uctx
  | None -> failwith "global uctx not set"

module LocalCtx = struct
  type t = Nt.t rty Typectx.ctx
  type mapping = (string, identifier) Hashtbl.t

  let cleanup (mapping : mapping) ~(recursive : bool) : unit =
    Hashtbl.to_seq mapping
    |> Seq.filter_map (fun (k, v) -> if k = v.x then None else Some v)
    |> Seq.iter (fun i ->
           if
             Rename.has_been_uniqified i.x
           then (
             assert (not (NameTracking.is_known i));
             NameTracking.remove_ast i ~recursive)
           else ())

  let contains_path_cond (Typectx.Typectx ctx : t) : bool =
    List.exists
      (fun { x; _ } -> String.starts_with ~prefix:path_condition_prefix x)
      ctx

  let eq (Typectx.Typectx l : t) (Typectx.Typectx r : t) : bool = l = r

  let layout (Typectx l : t) : string =
    List.map (fun { x; ty } -> x ^ " : " ^ layout_rty ty) l
    |> String.concat "\n"

  (** Combining to local contexts together with renaming *)
  let local_ctx_union_r (Typectx l : t) (r : t) : t * mapping =
    map_fst
      (fun (Typectx.Typectx res) ->
        (* TODO: Duplicates *)
        Typectx.Typectx (l @ res))
      (NameTracking.freshen r)

  (** Carefully adds the local context to uctx
    * You should probably use this for constructing uctx's *)
  let uctx_add_local_ctx (ctx : t) : uctx =
    let uctx = get_global_uctx () in
    {
      uctx with
      local_ctx =
        Typectx
          (List.concat [ Typectx.to_list ctx; Typectx.to_list uctx.local_ctx ]);
    }

  (** Take a local context and add the local context of a path which should have
   only path constraints and local vars.
    must not be incompatible contexts *)
  let promote_ctx_to_path (local_ctx : t) ~promote_ctx =
    (* TODO: How to assert that these contexts are not incompatible *)
    Typectx.Typectx (Typectx.to_list local_ctx @ Typectx.to_list promote_ctx)

  let exists_rtys_to_rty (Typectx.Typectx ctx) rty = exists_rtys_to_rty ctx rty
end
