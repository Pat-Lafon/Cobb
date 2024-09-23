open Typing
open Typing.Termcheck
open Language.FrontendTyped
open Utils
open Pieces
open Frontend_opt.To_typectx
open Zzdatatype.Datatype
open Tracking
open Language
open Context
open Relation
open Timeout

module TypeInference = struct
  type type_inf_result =
    | NoCoverage
    | FailedTyping
    | Res of (t rty, t rty term) typed

  let analyze_subtyping_result (new_rty : (t rty, t rty term) typed option) :
      type_inf_result =
    match new_rty with
    | Some new_rty ->
        if rty_is_false new_rty.ty then NoCoverage else Res new_rty
    | None -> FailedTyping

  let infer_type (uctx : uctx) (term : (Nt.t, Nt.t term) typed) =
    match Termcheck.term_type_infer_with_rec_check uctx term with
    | Some new_rty ->
        if rty_is_false new_rty.ty then NoCoverage else Res new_rty
    | None -> FailedTyping

  let check_filter_type (optional_filter_type : _ option) new_uctx
      (new_ut : (Nt.t rty, Nt.t rty term) typed) : bool =
    Option.fold ~none:false
      ~some:(fun filter_type ->
        match
          Timeout.sub_rty_bool_or_timeout new_uctx (new_ut.ty, filter_type)
        with
        | Result true -> false
        | _ -> (
            match
              Timeout.sub_rty_bool_or_timeout new_uctx (filter_type, new_ut.ty)
            with
            | Result true -> false
            | _ -> true))
      optional_filter_type
end

module type Block_intf = sig
  type t

  val layout : t -> string
  val to_nty : t -> Nt.t
  val to_typed_term : t -> (Nt.t, Nt.t term) typed
  val get_local_ctx : t -> LocalCtx.t
  val typing_relation : uctx -> t -> t -> Relations.relation
  val is_sub_rty : uctx -> t -> t -> bool
end

module ExistentializedBlock : sig
  type t = identifier * Nt.t rty

  val path_promotion : LocalCtx.t -> t -> t

  include Block_intf with type t := t
end = struct
  type t = identifier * Nt.t rty

  let to_typed_term ((name, ut) : t) : (Nt.t, Nt.t term) typed =
    NameTracking.get_term name

  let to_nty ((name, _) : t) : Nt.t = name.ty

  let layout ((name, ut) : t) : string =
    Printf.sprintf "%s : %s :\n%s\n"
      (NameTracking.get_term name |> layout_typed_erased_term)
      (layout_ty name.ty) (layout_rty ut)

  (* In the case of an existentialized block, the only thing in context is itself*)
  let get_local_ctx ((name, ext_rty) : t) : LocalCtx.t =
    Typectx.Typectx [ name.x #: ext_rty ]

  let new_X (x : identifier) (ty : Nt.t rty) : t = (x, ty)

  let is_sub_rty (uctx : uctx) ((name, ext_rty) : t) ((name', ext_rty') : t) :
      bool =
    Relations.is_sub_rty uctx ext_rty ext_rty'

  let typing_relation (uctx : uctx) ((name, ext_rty) : t)
      ((name', ext_rty') : t) : Relations.relation =
    Relations.typed_relation uctx name.x #: ext_rty name'.x #: ext_rty'

  let path_promotion (lc : LocalCtx.t) ((id, rt) : t) : t =
    let fresh_id = (Rename.unique id.x) #: id.ty in
    NameTracking.add_ast fresh_id (NameTracking.get_ast id |> Option.get);
    let fresh_rty = LocalCtx.exists_rtys_to_rty lc rt in

    assert (fresh_rty != rt);

    (fresh_id, fresh_rty)
end

module Block : sig
  type t = identifier * Nt.t rty * LocalCtx.t

  include Block_intf with type t := t

  val combine_all_args :
    t list -> identifier list * LocalCtx.t * LocalCtx.mapping list

  val existentialize : t -> ExistentializedBlock.t
end = struct
  type t = identifier * Nt.t rty * LocalCtx.t

  let to_typed_term ((name, ut, ctx) : t) : (Nt.t, Nt.t term) typed =
    NameTracking.get_term name

  let to_nty ((name, _, _) : t) : Nt.t = name.ty

  let layout ((name, ut, ctx) : t) : string =
    Printf.sprintf "%s ⊢ %s : %s :\n%s\n"
      (layout_typectx layout_rty ctx
      ^ if List.is_empty (Typectx.to_list ctx) then "" else " \n")
      (NameTracking.get_term name |> layout_typed_erased_term)
      (layout_ty name.ty) (layout_rty ut)

  let get_local_ctx ((name, ut, ctx) : t) : LocalCtx.t = ctx

  let existentialize ((name, ut, ctx) : t) : identifier * Nt.t rty =
    (* Kind of awkward, we want to filter out the current blocks name from the
       type(which would be redundant, unless that name is important) *)
    let local_ctx =
      Typectx.to_list ctx
      |> List.filter (fun { x; ty } ->
             if x = name.x then NameTracking.is_known x #: (erase_rty ty)
             else true)
    in
    let ext_rty = exists_rtys_to_rty local_ctx ut in
    (name, ext_rty)

  let is_sub_rty (uctx : uctx) (block : t) (block' : t) : bool =
    let id, target_ty, ctx = block in
    let id', ty, ctx' = block' in

    assert (not (LocalCtx.contains_path_cond ctx));
    assert (not (LocalCtx.contains_path_cond ctx'));

    let combined_ctx, mapping = LocalCtx.local_ctx_union_r ctx ctx' in
    let updated_ty = Pieces.ut_subst ty mapping in

    let res =
      Relations.is_sub_rty
        (LocalCtx.uctx_add_local_ctx combined_ctx)
        target_ty updated_ty
    in

    LocalCtx.cleanup mapping ~recursive:false;

    res

  let typing_relation (uctx : uctx) (target_block : t) (block : t) :
      Relations.relation =
    let target_id, target_ty, target_ctx = target_block in
    let id, ty, ctx = block in

    if LocalCtx.contains_path_cond target_ctx || LocalCtx.contains_path_cond ctx
    then
      ExistentializedBlock.typing_relation uctx
        (existentialize target_block)
        (existentialize block)
    else
      let combined_ctx, mapping = LocalCtx.local_ctx_union_r target_ctx ctx in
      let updated_ty = Pieces.ut_subst ty mapping in

      (* print_newline ();
         LocalCtx.layout combined_ctx |> print_endline;
         Printf.printf "target_ty: %s\n" (layout_rty target_ty);
         Printf.printf "updated_ty: %s\n" (layout_rty updated_ty); *)
      let res =
        Relations.typing_relation
          (LocalCtx.uctx_add_local_ctx combined_ctx)
          target_ty updated_ty
      in

      LocalCtx.cleanup mapping ~recursive:false;

      (*       Relations.layout res |> print_endline; *)
      res

  (* Takes vars with their own locals variables and constructs a list of
     arguments with a singular local context *)
  let combine_all_args (args : t list) :
      identifier list * LocalCtx.t * LocalCtx.mapping list =
    let arg_names = List.map (fun (id, _, _) -> id) args in
    let ctxs = List.map (fun (_, _, ctx) -> ctx) args in
    let unchanged_arg_name = List.hd arg_names in
    let unchanged_context = List.hd ctxs in
    List.fold_left2
      (fun ( (args : identifier list),
             (acc_context : LocalCtx.t),
             (new_id_list : LocalCtx.mapping list) ) (id : identifier)
           changed_ctx : (identifier list * LocalCtx.t * LocalCtx.mapping list) ->
        let new_ctx, mapping =
          LocalCtx.local_ctx_union_r acc_context changed_ctx
        in
        ( args
          @ [
              (match Hashtbl.find_opt mapping id.x with
              | Some s -> s
              | None ->
                  Printf.printf "id: %s\n" id.x;
                  List.iter (fun id -> Printf.printf "%s\n" id.x) args;
                  Hashtbl.iter
                    (fun k v -> Printf.printf "%s -> %s\n" k v.x)
                    mapping;
                  List.iter
                    (fun l -> layout_typectx layout_rty l |> print_endline)
                    ctxs;
                  failwith "you messed up");
            ],
          new_ctx,
          mapping :: new_id_list ))
      ([ unchanged_arg_name ], unchanged_context, [])
      (List.tl arg_names) (List.tl ctxs)
end

(* Take a term/block and see if it works inside of a path *)
(* Should probably only be used to promote a block to a path *)
let try_path path_ctx optional_filter_type ret_type (block_id, term, local_ctx)
    =
  assert (term.ty = block_id.ty);

  let new_path_ctx =
    LocalCtx.promote_ctx_to_path local_ctx ~promote_ctx:path_ctx
  in

  print_newline ();
  print_endline "Local Context";
  LocalCtx.layout local_ctx |> print_endline;
  print_endline "New Path Context";
  LocalCtx.layout new_path_ctx |> print_endline;

  let new_path_uctx = LocalCtx.uctx_add_local_ctx new_path_ctx in

  match TypeInference.infer_type new_path_uctx term with
  | Res new_ut ->
      assert (ret_type = erase_rty new_ut.ty);

      if
        TypeInference.check_filter_type optional_filter_type new_path_uctx
          new_ut
      then (
        print_endline "Didn't make path because of filter";
        None)
      else (
        print_endline "Found a path home";
        let new_path_ctx =
          Typectx.add_to_right new_path_ctx { x = block_id.x; ty = new_ut.ty }
        in
        Some (block_id, new_ut.ty, new_path_ctx)
        (* _add_to_path_specifc_list path_specific_list path_ctx
           (block_id, new_ut.ty, new_path_ctx)
           ret_type *))
  | _ ->
      print_endline "Other bad path cases";
      None

let apply (component : Pieces.component) (args : Block.t list) (ret_type : Nt.t)
    (filter_type : Nt.t rty option) (promotable_paths : LocalCtx.t list) =
  (* Correct joining of contexts? *)
  let ( (arg_names : identifier list),
        (joined_ctx : LocalCtx.t),
        (* That will need to be cleaned up *)
        (newly_created_ids : _) ) =
    Block.combine_all_args args
  in

  let block_id, term = Pieces.apply component arg_names in

  print_endline "Block in question:";
  LocalCtx.layout joined_ctx |> print_endline;
  layout_typed_erased_term term |> print_endline;

  assert (block_id.ty = ret_type);
  assert (term.ty = block_id.ty);

  let new_uctx : uctx = LocalCtx.uctx_add_local_ctx joined_ctx in

  (* This abstracts out the path trying logic in a somewhat not-nice
     way *)
  let try_add_paths () =
    let new_path_list =
      List.filter_map
        (fun path_ctx ->
          try_path path_ctx filter_type ret_type (block_id, term, joined_ctx)
          |> Option.map (fun ty -> (path_ctx, ty)))
        promotable_paths
    in

    (* Currenly, blocks are labelled when they are created, so we
       should delete them if they are never used *)
    (* Assumes that this is the only way to add the block*)
    if List.is_empty new_path_list then (
      print_endline "Block was not added";
      NameTracking.remove_ast block_id ~recursive:true;
      List.iter (LocalCtx.cleanup ~recursive:false) newly_created_ids)
    else print_endline "Block was added";
    new_path_list
  in

  (* Option.iter
     (fun ut ->
       print_endline "Considering block: ";
       Block.to_typed_term (block_id, ut.ty, joined_ctx)
       |> layout_typed_term |> print_endline)
     new_ut; *)
  match TypeInference.infer_type new_uctx term with
  | NoCoverage ->
      print_endline "No coverage";
      NameTracking.remove_ast block_id ~recursive:true;
      List.iter (LocalCtx.cleanup ~recursive:false) newly_created_ids;
      (None, [])
  | FailedTyping when List.is_empty promotable_paths ->
      print_endline "Failed typing with no chance of promotion";
      (None, [])
  | FailedTyping ->
      print_endline "Failed typing with chance of promotion";
      (* failed the new rec_check *)
      (None, try_add_paths ())
  | Res new_ut ->
      assert (ret_type = erase_rty new_ut.ty);
      if
        Option.is_some filter_type && not (List.is_empty promotable_paths)
        (* TODO: Possible optimization *) (* && (TypeInference.check_filter_type filter_type new_uctx new_ut) *)
      then (
        print_endline "Has filter so check in branch";
        (None, try_add_paths ()))
      else if
        (* Check if new term is coverage equivalent to one of it's
           arguments *)
        Relations.check_coverage_with_args new_uctx block_id new_ut.ty arg_names
      then (
        (* Ignore term if so *)
        print_endline "same as arg";
        NameTracking.remove_ast block_id ~recursive:true;
        List.iter (LocalCtx.cleanup ~recursive:false) newly_created_ids;
        (None, []))
      else if TypeInference.check_filter_type filter_type new_uctx new_ut then (
        (* Ignore term if so *)
        print_endline "Filtered out by type";
        NameTracking.remove_ast block_id ~recursive:true;
        List.iter (LocalCtx.cleanup ~recursive:false) newly_created_ids;
        (None, []))
      else (
        print_endline "new";
        let new_ctx =
          Typectx.add_to_right joined_ctx { x = block_id.x; ty = new_ut.ty }
        in
        assert (block_id.ty = ret_type);
        (Some (block_id, new_ut.ty, new_ctx), []))
