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

let max_cost_ref = ref 0

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

  (* let layout ({ general_coll; path_specific } : t) : string =
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
    } *)
end

module PrioritySynthesisCollection = struct
  type t = {
    path_specific :
      ( LocalCtx.t,
        ExistentializedBlock.t * PriorityBBMap.t * BlockMap.t )
      Hashtbl.t;
  }

  (** IDK, just call this initially but since branches get removed during
      synthesis *)
  let initialize_num_terms_considered ({ path_specific } : t) : unit =
    num_considered_terms :=
      Hashtbl.fold
        (fun _ (_, _, bmap) acc -> acc + BlockMap.size bmap)
        path_specific 0

  let assert_valid (t : t) : unit =
    Hashtbl.iter
      (fun _ (_, pbbm, bm) ->
        PriorityBBMap.assert_valid pbbm;
        BlockMap.assert_valid bm)
      t.path_specific

  (* TODO: Instead use lists not maps*)
  let init (inital_seeds : BlockMap.t) (target_ty : Nt.t rty)
      (path_specific_seeds : (LocalCtx.t, BlockMap.t) Hashtbl.t) : t =
    let inital_seeds = BlockMap.to_list inital_seeds in
    let target_block = ExistentializedBlock.create_target target_ty in
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
          let path_target_block =
            ExistentializedBlock.path_promotion p target_block
          in
          ( p,
            ( path_target_block,
              PriorityBBMap.init path_seeds,
              BlockMap.init path_seeds ) ))
        path_specific_seeds
    in

    { path_specific }

  (* todo: eventually deprecate *)
  let from_synth_coll ({ general_coll; path_specific } : SynthesisCollection.t)
      (target_ty : Nt.t rty) : t =
    let { new_blocks = new_general_blocks; old_blocks } : BlockCollection.t =
      general_coll
    in
    let new_general_blocks = BlockMap.to_list new_general_blocks in

    let target_block = ExistentializedBlock.create_target target_ty in

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

          let path_target_block =
            ExistentializedBlock.path_promotion lc target_block
          in

          ( lc,
            ( path_target_block,
              PriorityBBMap.init
                (List.append added_blocks (BlockMap.to_list new_blocks)),
              combined_block_map ) ))
        path_specific
    in
    let res = { path_specific } in
    assert_valid res;
    (*     failwith "stop here"; *)
    res

  let layout ({ path_specific } : t) : string =
    "Path Specific Collection:\n"
    ^ (Hashtbl.to_seq path_specific
      |> Seq.fold_left
           (fun acc (local_ctx, (_, block_collection, _)) ->
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

  (** Fold over all blocksets in any of the paths. Over the total collection of
      blocks for that type, not stratified by priority. Order unspecified. *)
  let fold_by_type (t : t) (nty : Nt.t) (acc : 'a)
      (f : 'a -> Blockset.BlockSet.t -> 'a) : 'a =
    Hashtbl.fold
      (fun _lc (_eblock, _pmap, bmap) acc ->
        let bset = BlockMap.get bmap nty in
        f acc bset)
      t.path_specific acc

  type block_map_rep = (* BlockRef of Block.t *  *) Block.t (* list *)

  let generalize_representative (b_list : Block.t list) : block_map_rep list =
    print_newline ();
    print_newline ();

    List.iter
      (fun b ->
        let b = { b with lc = b.lc |> LocalCtx.remove_duplicates } in

        Block.layout b |> print_endline)
      b_list;

    b_list

  let new_blocks_get_rep_or_nah (b_list : Block.t list)
      (target_block : ExistentializedBlock.t) :
      Block.t list * block_map_rep list =
    if List.length b_list <= 2 then (b_list, [])
    else
      let f, s =
        List.partition
          (fun b ->
            let res =
              ExistentializedBlock.is_sub_rty target_block (Block.existentialize b)

            in
            print_endline (b.id.x ^ ": " ^ string_of_bool res);
            (* if b.id.x = "idx379_0" then failwith "stop here to investigate"; *)
            res)
          b_list
      in
      (* if List.length s <= 2 then (
        failwith "do I hit this lol";
        (b_list, []))
      else  *)
      (f, generalize_representative s)

  let increment_by_path (lc : LocalCtx.t)
      ((pmap, bmap) : PriorityBBMap.t * BlockMap.t)
      ((component, (args_nty, ret_ty)) : Pieces.component * (Nt.t list * Nt.t))
      (cost : int) (target_block : ExistentializedBlock.t) :
      PriorityBBMap.t * BlockMap.t =
    print_endline ("Incrementing with op in path:\n" ^ LocalCtx.layout lc);
    let component_cost = Pieces.component_cost component in
    let possible_args =
      PriorityBBMap.get_args pmap (cost - component_cost) args_nty
    in

    let newly_created_terms =
      List.filter_map
        (fun args ->
          let pb = PreBlock.create component args ret_ty in

          if Option.is_some (PreBlock.additional_cost_from_diversity_penalty pb)
          then (
            print_endline "Diversity Penalty";
            PreBlock.layout pb |> print_endline;
            (* TODO: Lets do something better here *)
            None)
          else (
            print_endline "New PreBlock";
            print_endline (PreBlock.layout pb);

            let new_block = PreBlock.apply pb in

            new_block))
        possible_args
    in

    let just_blocks, reps =
      new_blocks_get_rep_or_nah newly_created_terms target_block
    in

    let bmap =
      List.fold_left
        (fun bmap b ->
          let size = BlockMap.size bmap in
          let bmap = BlockMap.add bmap b in
          if size = BlockMap.size bmap then ()
          else (
            print_endline "New Block Added";
            print_endline (Block.layout b);
            PriorityBBMap.add pmap b);
          ();
          bmap)
        bmap just_blocks
    in

    (* Just arbitrarily add them, TODO: We can do something better here *)
    if !max_cost_ref - 10 >= cost then
      List.iter (fun b -> PriorityBBMap.add pmap b) reps;

    (pmap, bmap)

  let increment_by_component ({ path_specific } : t)
      (component : Pieces.component * (Nt.t list * Nt.t)) (cost : int) =
    print_endline
      ("Incrementing with op: " ^ Pieces.layout_component (fst component));
    Hashtbl.iter
      (fun lc (pty, p, b) ->
        let pmap, bmap = increment_by_path lc (p, b) component cost pty in
        Hashtbl.replace path_specific lc (pty, pmap, bmap))
      path_specific
end
