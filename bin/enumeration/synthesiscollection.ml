open Blockcollection
open Context
open Utils
open Blockmap
open Frontend_opt.To_typectx
open Language.FrontendTyped
open Pieces
open Language

module SynthesisCollection = struct
  type t = {
    general_coll : BlockCollection.t;
    path_specific : (LocalCtx.t, BlockCollection.t) Hashtbl.t;
  }
  (** A set of block_collections, a general one and some path specific ones *)

  let init (inital_seeds : BlockMap.t)
      (path_specific_seeds : (LocalCtx.t, BlockMap.t) Hashtbl.t) : t =
    let general_coll : BlockCollection.t =
      { new_blocks = inital_seeds; old_blocks = [] }
    in
    let path_specific =
      Hashtbl.map
        (fun (lc, seeds) : (_ * BlockCollection.t) ->
          (lc, { new_blocks = seeds; old_blocks = [] }))
        path_specific_seeds
    in

    { general_coll; path_specific }

  let layout ({ general_coll; path_specific } : t) : string =
    "General Collection:\n"
    ^ BlockCollection.layout general_coll
    ^ "Path Specific Collection:\n"
    ^ (Hashtbl.to_seq path_specific
      |> Seq.fold_left
           (fun acc (local_ctx, block_collection) ->
             let res =
               layout_typectx layout_rty local_ctx
               ^ "\n"
               ^ BlockCollection.layout block_collection
             in
             acc ^ res)
           "")

  let print (coll : t) : unit = print_endline (layout coll)

  let merge_path_specific_maps
      (path_specific : (LocalCtx.t, BlockCollection.t) Hashtbl.t)
      (path_specific_maps : (LocalCtx.t, BlockMap.t) Hashtbl.t) :
      (LocalCtx.t, BlockCollection.t) Hashtbl.t =
    Hashtbl.iter
      (fun l m ->
        BlockMap.assert_valid m;
        assert (Hashtbl.mem path_specific l))
      path_specific_maps;

    Hashtbl.map
      (fun (l, bc) ->
        BlockCollection.assert_valid bc;
        match Hashtbl.find_opt path_specific_maps l with
        | Some b -> (l, BlockCollection.add_map_with_cov_checked bc b)
        | None -> (l, bc))
      path_specific

  let increment (collection : t)
      (operations : (Pieces.component * (Nt.t list * Nt.t)) list)
      (optional_filter_type : _ option) : t =
    (* We want to support the normal block_collection_increment as normal *)
    (* We want to be able to increment using new_seeds and old_seeds +
       old_general_seeds for path specific variations *)
    (* Still want to check for equivalence *)
    let general_new_blocks = collection.general_coll.new_blocks in
    let general_old_blocks = collection.general_coll.old_blocks in
    let promotable_paths =
      Hashtbl.to_seq_keys collection.path_specific |> List.of_seq
    in
    let path_specific_block_collections = collection.path_specific in

    let new_collection =
      {
        general_coll = BlockCollection.make_new_old collection.general_coll;
        path_specific =
          Hashtbl.map
            (fun (lc, path_specific_collection) ->
              (lc, BlockCollection.make_new_old path_specific_collection))
            path_specific_block_collections;
      }
    in

    (match optional_filter_type with
    | None -> print_endline "No filter type"
    | Some filter_type ->
        print_string "Filter type: ";
        print_endline (layout_rty filter_type));

    print_endline "Increment General Collection";

    let new_collection =
      (* Iterate over all components *)
      List.fold_left
        (fun { general_coll; path_specific } op ->
          print_endline
            ("Incrementing with op: " ^ Pieces.layout_component (fst op));

          let args =
            BlockMap.new_old_block_args general_new_blocks general_old_blocks
              (op |> snd |> fst)
          in

          let new_map, path_specific_maps =
            BlockMap.increment_by_args args op promotable_paths
              optional_filter_type
          in

          (* Iterate over sets of possible new maps *)
          (* let new_map, path_specific_maps =
               BlockMap.increment general_new_blocks general_old_blocks op
                 promotable_paths optional_filter_type
             in *)
          print_endline "general new_map";
          BlockMap.print new_map;
          print_endline "path_specific promotions";
          Hashtbl.iter
            (fun l m ->
              print_endline (layout_typectx layout_rty l);
              BlockMap.print m)
            path_specific_maps;

          BlockCollection.assert_valid general_coll;
          print_endline "Constructing new collection";
          {
            general_coll =
              BlockCollection.add_map_with_cov_checked general_coll new_map;
            path_specific =
              merge_path_specific_maps path_specific path_specific_maps;
          })
        new_collection operations
    in

    let path_specific_maps =
      Hashtbl.fold
        (fun local_ctx (path_col : BlockCollection.t) acc ->
          print_endline "Increment Path Specific Collection";
          print_endline (layout_typectx layout_rty local_ctx);
          let path_specific_map =
            List.fold_left
              (fun acc op ->
                print_endline
                  ("Incrementing with op in path: "
                  ^ Pieces.layout_component (fst op));

                let nt_args = op |> snd |> fst in

                let set_of_args =
                  BlockMap.union path_col.old_blocks general_old_blocks
                in

                assert (
                  if
                    not
                      (BlockMap.size set_of_args
                      = BlockMap.size path_col.old_blocks
                        + BlockMap.size general_old_blocks)
                  then (
                    print_endline "union";
                    BlockMap.print set_of_args;
                    print_endline "path";
                    BlockMap.print path_col.old_blocks;
                    print_endline "general";
                    BlockMap.print general_old_blocks;

                    failwith "bad size")
                  else true);

                (* This is the standard approach by looking at new path blocks *)
                let standard_args =
                  BlockMap.new_old_block_args path_col.new_blocks set_of_args
                    nt_args
                in

                let set_of_path_args =
                  BlockMap.union path_col.new_blocks path_col.old_blocks
                in

                assert (
                  if
                    not
                      (BlockMap.size set_of_path_args
                      = BlockMap.size path_col.new_blocks
                        + BlockMap.size path_col.old_blocks)
                  then (
                    print_endline "union";
                    BlockMap.print set_of_path_args;
                    print_endline "new";
                    BlockMap.print path_col.new_blocks;
                    print_endline "old";
                    BlockMap.print path_col.old_blocks;

                    failwith "bad size";
                    false)
                  else true);

                let args =
                  if List.length nt_args = 1 then standard_args
                  else
                    (* Alternatively, look at new general blocks with old stuff *)
                    let alternative_args =
                      BlockMap.req_req_args
                        (* First required set is the new general blocks*)
                        general_new_blocks
                        (* Second required is the path_blocks *)
                        set_of_path_args
                        (* Optional set is the old general blocks *)
                        general_old_blocks nt_args
                    in
                    Seq.append standard_args alternative_args
                in

                let path_op_specific_map, promoted_blocks =
                  BlockMap.increment_by_args args op [] optional_filter_type
                in
                assert (Hashtbl.is_empty promoted_blocks);

                BlockMap.print path_op_specific_map;

                BlockMap.union acc path_op_specific_map)
              (BlockMap.init []) operations
          in
          if BlockMap.is_empty path_specific_map then acc
          else (
            assert (not (Hashtbl.mem acc local_ctx));
            Hashtbl.replace acc local_ctx path_specific_map;
            acc))
        path_specific_block_collections (Hashtbl.create 5)
    in

    {
      new_collection with
      path_specific =
        merge_path_specific_maps new_collection.path_specific path_specific_maps;
    }
end
