open Typing
open Nt
open Typing.Termcheck
open Language.FrontendTyped
open Utils
open Pieces
open Frontend_opt.To_typectx
open Zzdatatype.Datatype
open Timeout
open Tracking
open Pomap
open Language
open Localctx

let global_uctx : uctx option ref = ref None

type subtypingres = NoOverlap | NotSubset | Res of (t rty, t rty term) typed

let analyze_subtyping_result (new_rty : (t rty, t rty term) typed option) :
    subtypingres =
  match new_rty with
  | Some new_rty -> (
      match new_rty.ty with
      | RtyBase { cty = Cty { phi = Lit { x = AC (B false); _ }; _ }; _ } ->
          NoOverlap
      | _ -> Res new_rty)
  | None -> NotSubset

module Block = struct
  type t = identifier * Nt.t rty * LocalCtx.t

  let to_typed_term ((name, ut, ctx) : t) : (Nt.t, Nt.t term) typed =
    NameTracking.get_term name

  let layout ((name, ut, ctx) : t) : string =
    Printf.sprintf "%s⊢ %s: %s :\n%s\n"
      (layout_typectx layout_rty ctx
      ^ if List.is_empty (Typectx.to_list ctx) then "" else " \n")
      (NameTracking.get_term name |> layout_typed_erased_term)
      (layout_ty name.ty) (layout_rty ut)
end

module rec RelationCache : sig
  val add : identifier -> identifier -> Relations.relation -> unit
  val check : identifier -> identifier -> Relations.relation option
  val reset_cache : unit -> unit
end = struct
  type t = (string * string, Relations.relation) Hashtbl.t

  let cache : t = Hashtbl.create 10000
  let reset_cache () = Hashtbl.clear cache

  let add (l : identifier) (r : identifier) (rel : Relations.relation) : unit =
    Hashtbl.add cache (l.x, r.x) rel

  let check (l : identifier) (r : identifier) : Relations.relation option =
    match Hashtbl.find_opt cache (l.x, r.x) with
    | Some r -> Some r
    | None ->
        Hashtbl.find_opt cache (r.x, l.x)
        |> Option.map Relations.invert_relation
end

and Relations : sig
  type relation = Equiv | ImpliesTarget | ImpliedByTarget | None | Timeout

  val layout : relation -> string
  val sexp_of_relation : relation -> Core.Sexp.t
  val is_equiv_or_timeout : relation -> bool
  val rty_typing_relation : uctx -> t rty -> t rty -> relation
  val block_typing_relation : uctx -> Block.t -> Block.t -> relation
  val invert_relation : relation -> relation
end = struct
  type relation = Equiv | ImpliesTarget | ImpliedByTarget | None | Timeout
  [@@deriving sexp]

  let layout relation = Core.Sexp.to_string_hum (sexp_of_relation relation)

  let invert_relation = function
    | Equiv -> Equiv
    | ImpliesTarget -> ImpliedByTarget
    | ImpliedByTarget -> ImpliesTarget
    | None -> None
    | Timeout -> Timeout

  let is_equiv_or_timeout (r : relation) : bool =
    match r with Equiv | Timeout -> true | _ -> false

  let diff_base_type (l : t rty) (r : t rty) : bool =
    not (erase_rty l = erase_rty r)

  let rty_typing_relation ctx target_ty ty =
    if diff_base_type target_ty ty then None
    else
      let implies_target =
        Timeout.sub_rty_bool_or_timeout ctx (ty, target_ty)
      in

      (* Short circuit on timeout *)
      if implies_target = Timeout then Timeout
      else
        (* Else continue *)
        let implied_by_target =
          Timeout.sub_rty_bool_or_timeout ctx (target_ty, ty)
        in
        match (implies_target, implied_by_target) with
        | Timeout, _ | _, Timeout -> Timeout
        | Result true, Result true -> Equiv
        | Result true, _ -> ImpliesTarget
        | _, Result true -> ImpliedByTarget
        | _ -> None

  let block_typing_relation (uctx : uctx) (target_block : Block.t)
      (block : Block.t) =
    let target_id, target_ty, target_ctx = target_block in
    let id, ty, ctx = block in

    match RelationCache.check target_id id with
    | Some r ->
        (* print_endline "in cache"; *)
        r
    | None ->
        let res =
          if diff_base_type target_ty ty then None
          else
            let combined_ctx, mapping =
              LocalCtx.local_ctx_union_r target_ctx ctx
            in
            let updated_ty = Pieces.ut_subst ty mapping in

            rty_typing_relation
              (LocalCtx.uctx_add_local_ctx uctx combined_ctx)
              target_ty updated_ty
        in
        RelationCache.add target_id id res;
        res
  (* |> fun res ->
     layout res |> print_endline;
     res *)
end

module BlockSet : sig
  type t

  val empty : t
  val singleton : Block.t -> t
  val add_block : t -> Block.t -> t
  val get_idx : t -> Ptset.elt -> Block.t
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val choose : t -> Block.t
  val to_list : t -> Block.t list
  val print : t -> unit
  val is_empty : t -> bool
  val fold : ('a -> Block.t -> 'a) -> 'a -> t -> 'a
  val get_succs : t -> Block.t -> Ptset.t
  val extract : t -> Block.t -> Block.t option * Ptset.t * Ptset.t
  val existentialize : t -> t
end = struct
  module P = Pomap_impl.Make (struct
    type el = Block.t
    type ord = Unknown | Lower | Equal | Greater

    let relations_to_ord = function
      | Relations.Equiv -> Equal
      | Relations.ImpliesTarget -> Lower
      | Relations.ImpliedByTarget -> Greater
      | Relations.None -> Unknown
      | Relations.Timeout -> Unknown

    let compare (a : el) (b : el) =
      let uctx = !global_uctx |> Option.get in
      Relations.block_typing_relation uctx a b |> relations_to_ord
  end)

  module D =
    Display_hasse_impl.Make
      (P)
      (struct
        include Display_hasse_impl.DefaultSpec

        type el = unit
        type 'a node = 'a P.node

        let pp_node_attr (ppf : Format.formatter) (node : el node) : unit =
          Format.fprintf ppf "label = \"%s\"" (P.get_key node |> Block.layout)

        let rotation = 0.
      end)

  type t = unit P.pomap

  let empty : t = P.empty
  let is_empty (pm : t) : bool = P.is_empty pm
  let singleton (x : Block.t) : t = P.singleton x ()
  let add_block (pm : t) x : t = P.add x () pm

  let get_idx (pm : t) (idx : Ptset.elt) : Block.t =
    P.find_ix idx pm |> P.get_key

  let choose (pm : t) : Block.t = P.choose pm |> snd |> P.get_key
  let union (l : t) (r : t) : t = P.union l r
  let inter (l : t) (r : t) : t = P.inter l r
  let diff (l : t) (r : t) : t = P.diff l r
  let print (pm : t) : unit = D.printf pm

  let to_list (pm : t) : P.key list =
    P.Store.fold (fun b acc -> P.get_key b :: acc) (P.get_nodes pm) []

  let fold (f : 'a -> P.key -> 'a) (acc : 'a) (pm : t) : 'a =
    P.fold (fun n acc -> f acc (P.get_key n)) pm acc

  let get_succs (pm : t) (b : P.key) : Ptset.t =
    P.find b pm |> snd |> P.get_sucs

  let extract (pm : t) (b : P.key) =
    let equal_block, n, pm =
      match P.add_find b () pm with
      | Found (_, n) ->
          (* print_endline "found"; *)
          (Some (P.get_key n), n, pm)
      | Added (_, n, new_pm) ->
          (* print_endline "added"; *)
          (None, n, new_pm)
    in

    (* print_endline "extracting for pm";
       print pm; *)
    let pred_blocks = P.get_prds n in
    let succ_blocks = P.get_sucs n in
    (equal_block, pred_blocks, succ_blocks)

  let existentialize (pm : t) : t =
    P.fold
      (fun n acc ->
        let id, rty, (local_ctx : LocalCtx.t) = P.get_key n in
        let local_ctx =
          Typectx.to_list local_ctx |> List.filter (fun { x; _ } -> x <> id.x)
        in
        let ext_rty = exists_rtys_to_rty local_ctx rty in
        add_block acc (id, ext_rty, Typectx.Typectx [ id.x #: ext_rty ]))
      pm P.empty
end

module BlockMap = struct
  type t = (Nt.t * BlockSet.t) list

  let empty : t = []

  let is_empty (map : t) : bool =
    List.for_all (fun (_, set) -> BlockSet.is_empty set) map

  (** Add the (type, term pair to the map) *)
  let rec add (map : t) (term : Block.t) (ty : Nt.t) : t =
    match map with
    | [] -> [ (ty, BlockSet.singleton term) ]
    | (ty', terms) :: rest ->
        if eq ty ty' then (ty, BlockSet.add_block terms term) :: rest
        else (ty', terms) :: add rest term ty

  (** Add the (type, term pair to the map) *)
  let rec add_list (map : t) (term_list : BlockSet.t) (ty : Nt.t) : t =
    match map with
    | [] -> [ (ty, term_list) ]
    | (ty', terms) :: rest ->
        if eq ty ty' then (ty, BlockSet.union terms term_list) :: rest
        else (ty', terms) :: add_list rest term_list ty

  let init (inital_seeds : (Block.t * Nt.t) list) : t =
    let aux (b_map : t) (term, ty) =
      (* layout_block term |> print_endline; *)
      add b_map term ty
    in
    List.fold_left aux [] inital_seeds

  let get_opt (map : t) (ty : Nt.t) : BlockSet.t option = List.assoc_opt ty map

  (** Gets the corresponding set or return  *)
  let get (map : t) (ty : Nt.t) : BlockSet.t =
    get_opt map ty |> Option.value ~default:BlockSet.empty

  let rec union (l_map : t) (r_map : t) : t =
    match l_map with
    | [] -> r_map
    | (ty, terms) :: rest ->
        let rest = union rest r_map in
        add_list rest terms ty

  let print (map : t) : unit =
    let aux (ty, terms) =
      Printf.printf "Type: %s\n" (layout_ty ty);
      BlockSet.print terms
    in
    List.iter aux map

  let check_coverage_with_args uctx block_id new_ut arg_names : bool =
    List.exists
      (fun ({ x; _ } as id : identifier) ->
        (*                    let joined_uctx = uctx_add_local_ctx uctx joined_ctx in *)
        let arg_t = FrontendTyped.get_opt uctx x |> Option.get in
        let relation_result =
          Relations.rty_typing_relation uctx arg_t new_ut.ty
        in
        let () = RelationCache.add id block_id relation_result in
        Relations.is_equiv_or_timeout relation_result)
      arg_names

  let rec _add_to_path_specifc_list (path_specific : (LocalCtx.t * t) list)
      (local_ctx : LocalCtx.t) (b : Block.t) ret_type =
    match path_specific with
    | [] -> [ (local_ctx, init [ (b, ret_type) ]) ]
    | (l, m) :: rest ->
        if l = local_ctx then (l, add m b ret_type) :: rest
        else (l, m) :: _add_to_path_specifc_list rest local_ctx b ret_type

  (* Promotable_paths should be empty if the new_blocks comes form a
       specific path *)
  (* Returns a block map for the new blocks... plus optionally a block map of
     those promoted to a new path *)
  (* Should we separate out the general and path specific cases? *)
  let increment (new_blocks : t) (old_blocks : t)
      ((component, (args, ret_type)) : Pieces.component * (Nt.t list * Nt.t))
      (promotable_paths : LocalCtx.t list) : t * (LocalCtx.t * t) list =
    let uctx = !global_uctx |> Option.get in

    (* Loop from 0 to args.len - 1 to choose an index for the `new_blocks` *)
    List.fold_left
      (fun acc new_set ->
        let l =
          List.mapi
            (fun j ty : Block.t list ->
              if List.mem j new_set then get new_blocks ty |> BlockSet.to_list
              else get old_blocks ty |> BlockSet.to_list)
            args
          |> n_cartesian_product
        in

        List.fold_left
          (fun (new_map, path_specific_list) (args : Block.t list) ->
            (* Correct joining of contexts? *)
            let (arg_names : identifier list), (joined_ctx : LocalCtx.t) =
              LocalCtx.combine_all_args args
            in

            let block_id, term = Pieces.apply component arg_names in

            let new_uctx : uctx = LocalCtx.uctx_add_local_ctx uctx joined_ctx in

            assert (term.ty = block_id.ty);

            let new_ut =
              Termcheck.term_type_infer_with_rec_check new_uctx
                { x = term.x; ty = block_id.ty }
            in

            match analyze_subtyping_result new_ut with
            | NoOverlap -> (new_map, path_specific_list)
            | NotSubset ->
                (* failed the new rec_check *)
                ( new_map,
                  (List.fold_left
                     (fun path_specific_list x ->
                       let new_path_ctx =
                         LocalCtx.promote_ctx_to_path joined_ctx ~promote_ctx:x
                       in

                       let new_path_uctx =
                         LocalCtx.uctx_add_local_ctx uctx new_path_ctx
                       in

                       let new_path_ut =
                         Termcheck.term_type_infer_with_rec_check new_path_uctx
                           { x = term.x; ty = block_id.ty }
                       in
                       match analyze_subtyping_result new_path_ut with
                       | Res new_ut ->
                           let new_path_ctx =
                             Typectx.add_to_right new_path_ctx
                               { x = block_id.x; ty = new_ut.ty }
                           in
                           _add_to_path_specifc_list path_specific_list x
                             (block_id, new_ut.ty, new_path_ctx)
                             ret_type
                       | _ -> path_specific_list)
                     path_specific_list)
                    promotable_paths )
            | Res new_ut ->
                (* Check if new term is coverage equivalent to one of it's
                   arguments *)
                if check_coverage_with_args new_uctx block_id new_ut arg_names
                then (* Ignore term if so *)
                  (new_map, path_specific_list)
                else
                  let new_ctx =
                    Typectx.add_to_right joined_ctx
                      { x = block_id.x; ty = new_ut.ty }
                  in
                  ( add new_map (block_id, new_ut.ty, new_ctx) ret_type,
                    path_specific_list ))
          acc l)
      (empty, [])
      (range (List.length args) |> superset)
end

module BlockCollection = struct
  (* Blocks are added to the `new_blocks` field *)
  (* `new_blocks` get shifted over to `old_blocks` when we increment to a new, larger set of blocks *)
  type t = { new_blocks : BlockMap.t; old_blocks : BlockMap.t }

  (** Initialize a block collection with the given seeds values
    * Seeds are initial blocks that are just variables, constants, or operations that take no arguments (or just unit) *)
  let init (inital_seeds : (Block.t * Nt.t) list) : t =
    let new_blocks : BlockMap.t = BlockMap.init inital_seeds in
    { new_blocks; old_blocks = [] }

  let print ({ new_blocks; old_blocks } : t) : unit =
    Printf.printf "New Blocks:\n";
    BlockMap.print new_blocks;
    Printf.printf "Old Blocks:\n";
    BlockMap.print old_blocks

  let make_new_old ({ new_blocks; old_blocks } : t) : t =
    { new_blocks = []; old_blocks = BlockMap.union new_blocks old_blocks }

  (** For the block inference
    * Returns a mapping of all blocks, new and old *)
  let get_full_map ({ new_blocks; old_blocks } : t) : BlockMap.t =
    BlockMap.union new_blocks old_blocks

  let rec add_map_with_cov_checked coll (map : BlockMap.t) =
    match map with
    | [] -> coll
    | (ty, set) :: rest ->
        let { new_blocks; old_blocks } : t =
          add_map_with_cov_checked coll rest
        in
        assert (not (List.mem_assoc ty new_blocks));
        let old_set = BlockMap.get old_blocks ty in
        let new_set = BlockSet.diff set old_set in
        { new_blocks = (ty, new_set) :: new_blocks; old_blocks }
end

module SynthesisCollection = struct
  type t = {
    general_coll : BlockCollection.t;
    path_specific : (LocalCtx.t * BlockCollection.t) list;
  }
  (** A set of block_collections, a general one and some path specific ones *)

  let init (inital_seeds : BlockMap.t)
      (path_specific_seeds : (LocalCtx.t * BlockMap.t) list) : t =
    let general_coll : BlockCollection.t =
      { new_blocks = inital_seeds; old_blocks = [] }
    in
    let path_specific =
      List.map
        (fun (ctx, seeds) : (_ * BlockCollection.t) ->
          (ctx, { new_blocks = seeds; old_blocks = [] }))
        path_specific_seeds
    in
    { general_coll; path_specific }

  let print ({ general_coll; path_specific } : t) : unit =
    Printf.printf "General Collection:\n";
    BlockCollection.print general_coll;
    Printf.printf "Path Specific Collection:\n";
    List.iter
      (fun (local_ctx, block_collection) ->
        layout_typectx layout_rty local_ctx |> print_endline;
        BlockCollection.print general_coll)
      path_specific

  (* First list must be a superset of the second in terms of local_ctx used*)
  let merge_path_specific_maps
      (path_specific : (LocalCtx.t * BlockCollection.t) list)
      (path_specific_maps : (LocalCtx.t * BlockMap.t) list) :
      (LocalCtx.t * BlockCollection.t) list =
    assert (List.length path_specific >= List.length path_specific_maps);
    List.map
      (fun (l, bc) ->
        match List.assoc_opt l path_specific_maps with
        | Some b -> (l, BlockCollection.add_map_with_cov_checked bc b)
        | None -> (l, bc))
      path_specific

  let increment (collection : t)
      (operations : (Pieces.component * (Nt.t list * Nt.t)) list) : t =
    (* We want to support the normal block_collection_increment as normal *)
    (* We want to be able to increment using new_seeds and old_seeds +
       old_general_seeds for path specific variations *)
    (* Still want to check for equivalence *)
    let general_new_blocks = collection.general_coll.new_blocks in
    let general_old_blocks = collection.general_coll.old_blocks in
    let promotable_paths = List.map fst collection.path_specific in
    let path_specific_block_collections = collection.path_specific in

    let new_collection =
      {
        general_coll = BlockCollection.make_new_old collection.general_coll;
        path_specific =
          List.map
            (fun (ctx, path_specific_collection) ->
              (ctx, BlockCollection.make_new_old path_specific_collection))
            path_specific_block_collections;
      }
    in

    let new_collection =
      (* Iterate over all components *)
      List.fold_left
        (fun { general_coll; path_specific } op ->
          (* Iterate over sets of possible new maps *)
          let new_map, path_specific_maps =
            BlockMap.increment general_new_blocks general_old_blocks op
              promotable_paths
          in

          {
            general_coll =
              BlockCollection.add_map_with_cov_checked general_coll new_map;
            path_specific =
              merge_path_specific_maps path_specific path_specific_maps;
          })
        new_collection operations
    in

    let path_specific_maps =
      List.fold_left
        (fun acc (local_ctx, (path_col : BlockCollection.t)) ->
          let path_specific_map =
            List.fold_left
              (fun acc op ->
                let path_op_specific_map, promoted_blocks =
                  BlockMap.increment path_col.new_blocks
                    (BlockMap.union path_col.old_blocks general_old_blocks)
                    op []
                in
                assert (List.is_empty promoted_blocks);
                BlockMap.union acc path_op_specific_map)
              (BlockMap.init []) operations
          in
          if BlockMap.is_empty path_specific_map then acc
          else (local_ctx, path_specific_map) :: acc)
        [] path_specific_block_collections
    in

    {
      new_collection with
      path_specific =
        merge_path_specific_maps new_collection.path_specific path_specific_maps;
    }
end

module Extraction = struct
  (* https://codereview.stackexchange.com/questions/40366/combinations-of-size-k-from-a-list-in-ocaml
    *)
  let rec combnk k lst =
    if k = 0 then [ [] ]
    else
      let rec inner = function
        | [] -> []
        | x :: xs -> List.map (fun z -> x :: z) (combnk (k - 1) xs) :: inner xs
      in
      List.concat (inner lst)

  (* Helper function to get the current rty of terms under consideration *)
  let unioned_rty_type (l : (LocalCtx.t * (identifier * t rty) * Ptset.t) list)
      : t rty =
    List.map (fun (_, (_, rt), _) -> rt) l |> union_rtys

  (* Helper function to get the current rty of terms under consideration *)
  let unioned_rty_type2
      (l : (LocalCtx.t * BlockSet.t * (identifier * t rty) * Ptset.t) list) :
      t rty =
    List.map (fun (_, _, (_, rt), _) -> rt) l |> union_rtys

  (* Try to find the largest block that can be removed *)
  let minimize_once (x : (LocalCtx.t * (identifier * t rty) * Ptset.t) list)
      (target_ty : t rty) : (LocalCtx.t * (identifier * t rty) * Ptset.t) list =
    if List.length x = 1 then x
    else
      let () = assert (List.length x > 1) in

      let uctx = !global_uctx |> Option.get in

      print_endline (layout_rty target_ty);

      (* Assert that current min passes subtyping check *)
      assert (sub_rty_bool uctx (unioned_rty_type x, target_ty));

      let current_min = unioned_rty_type x in

      print_endline (unioned_rty_type x |> layout_rty);

      let res =
        List.fold_left
          (fun (current_min, current_list) proposed_list ->
            let proposed_min = unioned_rty_type proposed_list in
            if
              (* The proposed min implies the target*)
              sub_rty_bool uctx (proposed_min, target_ty)
              && (* And it is implied by the current min*)
              sub_rty_bool uctx (current_min, proposed_min)
            then (proposed_min, proposed_list)
            else (current_min, current_list))
          (current_min, x)
          (combnk (List.length x - 1) x)
        |> snd
      in

      assert (sub_rty_bool uctx (unioned_rty_type res, target_ty));
      res

  (* Repeat trying to reduce the number of blocks until minimum is found *)
  let minimize_num (x : (LocalCtx.t * (identifier * t rty) * Ptset.t) list)
      (target_ty : t rty) : (LocalCtx.t * (identifier * t rty) * Ptset.t) list =
    let rec aux (x : (LocalCtx.t * (identifier * t rty) * Ptset.t) list) =
      let new_x = minimize_once x target_ty in
      if List.length new_x < List.length x then aux new_x else new_x
    in
    aux x

  let rec minimize_type_helper (map : BlockSet.t) (target_ty : t rty)
      (acc : 'a list) (remaining_set : Ptset.t) (current_minimum : t rty) :
      ('a list * t rty) option =
    if Ptset.is_empty remaining_set then None
    else
      let idx = Ptset.max_elt remaining_set in
      let new_term = BlockSet.get_idx map idx in
      let id, rty, lc = new_term in

      let new_term_succs = BlockSet.get_succs map new_term in

      let new_thing : LocalCtx.t * (identifier * t rty) * Ptset.t =
        (lc, (id, rty), new_term_succs)
      in

      let new_covered_rty = unioned_rty_type (new_thing :: acc) in

      let uctx = !global_uctx |> Option.get in

      if sub_rty_bool uctx (new_covered_rty, target_ty) then
        if sub_rty_bool uctx (current_minimum, new_covered_rty) then
          Some (new_thing :: acc, new_covered_rty)
        else
          minimize_type_helper map target_ty acc
            (Ptset.remove idx remaining_set)
            current_minimum
      else
        (* Other successors to draw on if not sufficient in hitting the target
           type *)
        let other_succs = Ptset.diff remaining_set new_term_succs in
        minimize_type_helper map target_ty (new_thing :: acc) other_succs
          current_minimum

  (* Try to reduce coverage of a specific term*)
  let minimize_type (map : BlockSet.t)
      (x : (LocalCtx.t * (identifier * t rty) * Ptset.t) list)
      (target_ty : t rty) : (LocalCtx.t * (identifier * t rty) * Ptset.t) list =
    let uctx = !global_uctx |> Option.get in
    let current_coverage_type = unioned_rty_type x in
    assert (sub_rty_bool uctx (current_coverage_type, target_ty));

    List.fold_left
      (fun (current_min_coverage, (acc : _ list)) idx : (t rty * _ list) ->
        let current_term, rest_terms =
          Core.List.drop x idx |> List.destruct_opt |> Option.get
        in

        let lc, (_, _), ptset = current_term in

        if Ptset.is_empty ptset then
          (* Bail out if there are no other possible options*)
          ( current_min_coverage,
            List.concat [ acc; [ current_term ]; rest_terms ] )
        else
          let _ = (current_min_coverage, [ current_term ]) in

          match
            minimize_type_helper map target_ty
              (List.concat [ acc; rest_terms ])
              ptset current_min_coverage
          with
          | None -> (current_min_coverage, acc)
          | Some (interesting_terms, new_min_coverage) ->
              (new_min_coverage, List.append interesting_terms acc))
      (current_coverage_type, [])
      (range (List.length x))
    |> snd

  (* Try to increase the coverage of a specific term to satisfy
     the target type *)
  let setup_type (x : (LocalCtx.t * BlockSet.t * (Ptset.t * Ptset.t)) list)
      (target_ty : t rty) :
      (LocalCtx.t * BlockSet.t * (identifier * t rty) * Ptset.t) list =
    let uctx = !global_uctx |> Option.get in

    (* print_endline (layout_rty target_ty); *)
    let res =
      List.map
        (fun (lc, map, (over_set, under_set)) ->
          (* BlockSet.print map; *)
          match Ptset.min_elt_opt over_set with
          | Some i ->
              let id, rty, _lc = BlockSet.get_idx map i in
              assert (_lc = lc);
              (lc, map, (id, rty), under_set)
          | None ->
              let idx = Ptset.max_elt under_set in
              let id, rty, _lc = BlockSet.get_idx map idx in

              (* print_endline (layout_typectx layout_rty lc);
                 print_endline (layout_typectx layout_rty _lc);

                 print_endline (layout_rty rty); *)
              assert (_lc = lc);
              (lc, map, (id, rty), Ptset.remove idx under_set))
        x
    in
    assert (sub_rty_bool uctx (unioned_rty_type2 res, target_ty));
    res

  let path_promotion lc acc (id, rt, block_ctx) =
    let new_context, mapping = NameTracking.freshen block_ctx in
    let fresh_id = (Hashtbl.find mapping id.x) #: id.ty in
    let fresh_rt = Pieces.ut_subst rt mapping in
    NameTracking.add_ast fresh_id (NameTracking.get_ast id |> Option.get);
    BlockSet.add_block acc
      ( fresh_id,
        fresh_rt,
        LocalCtx.promote_ctx_to_path new_context ~promote_ctx:lc )

  (* Take blocks of different coverage types and join them together into full programs using non-deterministic choice *)
  let extract_blocks (collection : SynthesisCollection.t) (target_ty : t rty) :
      (LocalCtx.t * Block.t) list =
    let target_nty = erase_rty target_ty in
    let uctx = !global_uctx |> Option.get in
    RelationCache.reset_cache ();

    (* Create a target block that we are missing *)
    let target_block : Block.t =
      ( (Rename.unique "missing") #: target_nty |> NameTracking.known_var,
        target_ty,
        Typectx.emp )
    in

    (* Get all blocks from the general collection *)
    let general_set =
      BlockCollection.get_full_map collection.general_coll |> fun x ->
      BlockMap.get x target_nty |> BlockSet.existentialize
    in

    (* Printf.printf "\n\n Generall collection we are interested in\n";
       BlockSet.print general_set; *)
    let equal_block, _pred_blocks, _succ_blocks =
      BlockSet.extract general_set target_block
    in

    assert (List.length collection.path_specific > 0);

    match equal_block with
    | Some b ->
        (* print_endline (Block.layout b); *)
        let current : (LocalCtx.t * (identifier * t rty) * Ptset.t) list =
          List.map
            (fun (lc, _) ->
              let id, rty, _ =
                path_promotion lc BlockSet.empty b
                |> BlockSet.existentialize |> BlockSet.choose
              in
              (lc, (id, rty), Ptset.empty))
            collection.path_specific
        in

        let current = minimize_num current target_ty in

        List.map (fun (lc, (id, rty), _) -> (lc, (id, rty, lc))) current
    | _ -> (
        (* Get the sets for each path *)
        let path_specific_sets =
          List.map
            (fun (lc, bc) ->
              BlockCollection.get_full_map bc |> fun x ->
              BlockMap.get_opt x target_nty
              |> Option.value ~default:BlockSet.empty
              |> BlockSet.existentialize
              |> fun x -> (lc, x))
            collection.path_specific
        in

        (* We are going to do some normalization setup *)
        (* All General terms are going to get pushed into paths *)
        let path_specific_sets =
          List.map
            (fun (lc, bs) ->
              (lc, BlockSet.fold (path_promotion lc) bs general_set))
            path_specific_sets
        in

        (* Printf.printf "\n\n Path Specific collections we are interested in\n";
           List.iter
             (fun (ctx, set) ->
               Printf.printf "Path Specific Collection: %s\n"
                 (layout_typectx layout_rty ctx);
               BlockSet.print set)
             path_specific_sets; *)
        let block_options_in_each_path =
          List.map
            (fun (lc, bs) -> (lc, bs, BlockSet.extract bs target_block))
            path_specific_sets
        in

        match
          List.find_opt
            (fun (_, _, (eq, _, _)) -> Option.is_some eq)
            block_options_in_each_path
        with
        | Some ((lc, _, (Some b, _, _)) as s) ->
            (* print_endline (layout_typectx layout_rty lc);
               print_endline (Block.layout b);
               print_endline "We just shortcircuit in this case"; *)
            [ (lc, b) ]
        | _ ->
            (* Filter out those equal terms then to make my life cleaner *)
            let block_options_in_each_path =
              List.map
                (fun (lc, bs, (_, p, s)) ->
                  assert (not (Ptset.is_empty p && Ptset.is_empty s));
                  (lc, bs, (p, s)))
                block_options_in_each_path
            in

            let _ = setup_type block_options_in_each_path target_ty in

            failwith "unimplemented")

  (* let new_path_ctx =
                     promote_ctx_to_path new_uctx.local_ctx ~promote_ctx:x
                   in *)

  (* When does repair happen? Now? Or do I extract this out? *)
end

module Synthesis = struct
  let rec synthesis_helper (max_depth : int) (target_type : t rty)
      (collection : SynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list) :
      (LocalCtx.t * _ list) list =
    match max_depth with
    | 0 ->
        (* SynthesisCollection.print collection; *)
        (* Join blocks together into programs *)
        Extraction.extract_blocks collection target_type
        |> List.map (fun (lc, b) -> (lc, Block.to_typed_term b))
        |> group_by (fun (x, y) -> x)
    | depth ->
        let operations =
          if depth == 1 then
            let nty = erase_rty target_type in
            List.filter (fun (p, (_, ret_ty)) -> ret_ty = nty) operations
          else operations
        in
        (* If not, increment the collection and try again *)
        synthesis_helper (depth - 1) target_type
          (SynthesisCollection.increment collection operations)
          operations

  (** Given some initial setup, run the synthesis algorithm *)
  let synthesis (target_type : t rty) (max_depth : int)
      (inital_seeds : SynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list) :
      (LocalCtx.t * _) list =
    (* SynthesisCollection.print inital_seeds; *)
    synthesis_helper max_depth target_type inital_seeds operations
end
