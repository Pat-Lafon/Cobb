open Language.FrontendTyped
open Utils
open Frontend_opt.To_typectx
open Tracking
open Language

module LocalCtx = struct
  type t = Nt.t rty Typectx.ctx

  (* Combining to local contexts together with renaming *)
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

  let promote_ctx_to_path (local_ctx : t) ~promote_ctx =
    Typectx.Typectx (Typectx.to_list local_ctx @ Typectx.to_list promote_ctx)

  let combine_all_args args =
    let arg_names = List.map (fun (id, _, _) -> id) args in
    let ctxs = List.map (fun (_, _, ctx) -> ctx) args in
    let unchanged_arg_name = List.hd arg_names in
    let unchanged_context = List.hd ctxs in
    List.fold_left2
      (fun ((args : identifier list), (acc_context : t)) (id : identifier)
           changed_ctx : (identifier list * t) ->
        let new_ctx, mapping = local_ctx_union_r acc_context changed_ctx in
        ( args
          @ [
              (match Hashtbl.find_opt mapping id.x with
              | Some s -> s
              | None ->
                  Printf.printf "id: %s\n" id.x;
                  List.iter (fun id -> Printf.printf "%s\n" id.x) args;
                  Hashtbl.iter
                    (fun k v -> Printf.printf "%s -> %s\n" k v)
                    mapping;
                  List.iter
                    (fun l -> layout_typectx layout_rty l |> print_endline)
                    ctxs;
                  failwith "you messed up")
              #: id.ty;
            ],
          new_ctx ))
      ([ unchanged_arg_name ], unchanged_context)
      (List.tl arg_names) (List.tl ctxs)
end
