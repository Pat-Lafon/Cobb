open Language.FrontendTyped
open Utils
open Tracking
open Language

module LocalCtx = struct
  type t = Nt.t rty Typectx.ctx

  (** Combining to local contexts together with renaming *)
  let local_ctx_union_r (Typectx l : t) (r : t) : t * (string, string) Hashtbl.t
      =
    map_fst
      (fun (Typectx.Typectx res) ->
        (* TODO: Duplicates *)
        Typectx.Typectx (l @ res))
      (NameTracking.freshen r)

  (** Carefully adds the local context to uctx
    * You should probably use this for constructing uctx's *)
  let uctx_add_local_ctx (uctx : uctx) (ctx : t) : uctx =
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
