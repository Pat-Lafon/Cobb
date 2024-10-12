open Blockcollection
open Context
open Utils
open Blockmap
open Frontend_opt.To_typectx
open Language.FrontendTyped
open Pieces
open Language
open Block
open Blockqueue

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
            |> Seq.map (fun args ->
                   PreBlock.create (fst op) args (snd op |> snd))
          in

          let new_map, path_specific_maps =
            BlockMap.increment_by_args args promotable_paths
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

                let args =
                  Seq.map
                    (fun args -> PreBlock.create (fst op) args (snd op |> snd))
                    args
                in

                let path_op_specific_map, promoted_blocks =
                  BlockMap.increment_by_args args [] optional_filter_type
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

module PrioritySynthesisCollection = struct
  type t = {
    path_specific : (LocalCtx.t, PriorityBBMap.t * BlockMap.t) Hashtbl.t;
  }

  let assert_valid (t : t) : unit =
    Hashtbl.iter
      (fun _ (pbbm, bm) ->
        PriorityBBMap.assert_valid pbbm;
        BlockMap.assert_valid bm)
      t.path_specific

  (* TODO: Instead use lists not maps*)
  let init (inital_seeds : BlockMap.t)
      (path_specific_seeds : (LocalCtx.t, BlockMap.t) Hashtbl.t) : t =
    let inital_seeds = BlockMap.to_list inital_seeds in
    let path_specific =
      Hashtbl.map
        (fun (p, seeds) ->
          let path_seeds =
            List.append (BlockMap.to_list seeds)
              (List.map
                 (fun ({ lc; _ } as b : block_record) : block_record ->
                   let new_path_ctx =
                     LocalCtx.promote_ctx_to_path lc ~promote_ctx:p
                   in
                   { b with lc = new_path_ctx })
                 inital_seeds)
          in
          (p, (PriorityBBMap.init path_seeds, BlockMap.init path_seeds)))
        path_specific_seeds
    in

    { path_specific }

  (* todo: eventually deprecate *)
  let from_synth_coll ({ general_coll; path_specific } : SynthesisCollection.t)
      : t =
    let { new_blocks = new_general_blocks; old_blocks } : BlockCollection.t =
      general_coll
    in
    let new_general_blocks = BlockMap.to_list new_general_blocks in

    assert (BlockMap.is_empty old_blocks);
    let path_specific =
      Hashtbl.map
        (fun (lc, ({ new_blocks; old_blocks } : BlockCollection.t)) ->
          assert (BlockMap.is_empty old_blocks);

          let path_general_blocks =
            List.map (fun b -> Block.path_promotion lc b) new_general_blocks
          in

          let combined_block_map, added_blocks =
            List.fold_left
              (fun (acc_map, acc_list) pgb ->
                let og_size = BlockMap.size acc_map in
                let acc_map = BlockMap.add acc_map pgb in
                if og_size = BlockMap.size acc_map then (acc_map, acc_list)
                else (acc_map, pgb :: acc_list))
              (new_blocks, []) path_general_blocks
          in
          ( lc,
            ( PriorityBBMap.init
                (List.append added_blocks (BlockMap.to_list new_blocks)),
              combined_block_map ) ))
        path_specific
    in
    let res = { path_specific } in
    assert_valid res;
    res

  let layout ({ path_specific } : t) : string =
    "Path Specific Collection:\n"
    ^ (Hashtbl.to_seq path_specific
      |> Seq.fold_left
           (fun acc (local_ctx, (block_collection, _)) ->
             let res =
               "In Path:\n"
               ^ layout_typectx layout_rty local_ctx
               ^ "\n"
               ^ PriorityBBMap.layout block_collection
             in
             acc ^ res)
           "")

  let print (t : t) : unit = print_endline (layout t)

  let remove_finished_contexts (t : t) (lc_list : LocalCtx.t list) : unit =
    List.iter
      (fun lc ->
        assert (Hashtbl.mem t.path_specific lc);
        Hashtbl.remove t.path_specific lc)
      lc_list

  let increment_by_path (lc : LocalCtx.t)
      ((pmap, bmap) : PriorityBBMap.t * BlockMap.t)
      ((component, (args_nty, ret_ty)) : Pieces.component * (Nt.t list * Nt.t))
      (cost : int) : PriorityBBMap.t * BlockMap.t =
    print_endline ("Incrementing with op in path:\n" ^ LocalCtx.layout lc);
    let component_cost = Pieces.component_cost component in
    let possible_args =
      PriorityBBMap.get_args pmap (cost - component_cost) args_nty
    in

    let bmap =
      List.fold_left
        (fun bmap args ->
          let pb = PreBlock.create component args ret_ty in

          print_endline "New PreBlock";
          print_endline (PreBlock.layout pb);

          let new_block = PreBlock.apply pb in

          match new_block with
          | None -> bmap
          | Some b ->
              let size = BlockMap.size bmap in
              let bmap = BlockMap.add bmap b in
              if size = BlockMap.size bmap then ()
              else (
                print_endline "New Block Added";
                print_endline (Block.layout b);
                PriorityBBMap.add pmap b);
              ();
              bmap)
        bmap possible_args
    in
    (pmap, bmap)

  let increment_by_component ({ path_specific } : t)
      (component : Pieces.component * (Nt.t list * Nt.t)) (cost : int) =
    print_endline
      ("Incrementing with op: " ^ Pieces.layout_component (fst component));
    Hashtbl.iter
      (fun lc path_maps ->
        let pmap, bmap = increment_by_path lc path_maps component cost in
        Hashtbl.replace path_specific lc (pmap, bmap))
      path_specific
end