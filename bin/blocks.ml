open Zutils
open Utils
open Pieces
open Language
open Context
open Block
open Blockset
open Blockmap
open Extraction
open Synthesiscollection

let check_paths_for_solution (collection : PrioritySynthesisCollection.t) :
    (LocalCtx.t * _) list =
  Hashtbl.fold
    (fun lc (path_target_block, _, bmap) acc ->
      let nty = ExistentializedBlock.to_nty path_target_block in
      (* todo better *)
      let s = BlockMap.existentialized_list bmap nty |> BlockSetE.init in

      let res = Extraction.extract_for_path lc path_target_block s in
      List.append res acc)
    collection.path_specific []

let check_and_remove_finished_paths (coll : PrioritySynthesisCollection.t) :
    (LocalCtx.t * _) list =
  let paths_finished_by_seeds = check_paths_for_solution coll in

  let completed_contexts =
    List.map fst paths_finished_by_seeds
    |> List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) []
  in

  PrioritySynthesisCollection.remove_finished_contexts coll completed_contexts;
  paths_finished_by_seeds

let _num_target_blocks (collection : PrioritySynthesisCollection.t)
    (target_type : rty) : int =
  let nty_target_type = erase_rty target_type in
  PrioritySynthesisCollection.fold_by_type collection nty_target_type 0
    (fun acc bset -> acc + BlockSet.size bset)

let imprecise = ref false

module PrioritySynthesis = struct
  let rec synthesis_helper (target_type : rty) (current_cost : int)
      (*      (priority_queue : PathPriorityQueue.t) *)
        (collection : PrioritySynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list)
      (collection_file : string) (acc : (LocalCtx.t * _) list) :
      (LocalCtx.t * _) list =
    if !max_cost_ref < current_cost then
      if !imprecise then
        let target_nty = erase_rty target_type in
        let list_of_paths = Hashtbl.to_seq collection.path_specific in
        let found_less_precise_solutions =
          Seq.map
            (fun (lc, (target_block, (pmap : Blockqueue.PriorityBBMap.t), bmap))
               ->
              let (blocks : Block.t list) =
                Blockqueue.PriorityBBMap.get_all_blocks_of_type pmap target_nty
              in

              let lattice =
                BlockMap.existentialized_list bmap target_nty |> BlockSetE.init
              in

              Extraction.extract_imprecise_solution lc target_block blocks
                lattice)
            list_of_paths
        in
        List.of_seq found_less_precise_solutions
        |> List.flatten |> List.append acc
      else failwith "Max cost exceeded"
    else (
      print_endline "Current Collection";

      (*     PrioritySynthesisCollection.print collection;
    Core.Out_channel.write_all collection_file
      ~data:(PrioritySynthesisCollection.layout collection); *)
      let current_target_amount = _num_target_blocks collection target_type in

      print_endline
        ("Current number of extraction blocks to choose from: "
        ^ string_of_int current_target_amount);

      let _ =
        List.fold_left
          (fun acc component ->
            PrioritySynthesisCollection.increment_by_component acc component
              current_cost;
            acc)
          collection operations
      in

      let new_target_amount = _num_target_blocks collection target_type in

      let path_solutions =
        (* only check in paths that have gotten something new lol *)
        if current_target_amount = new_target_amount then (
          print_endline "No new blocks have been added, avoid extraction";
          [])
        else check_and_remove_finished_paths collection
      in

      let acc = path_solutions @ acc in

      if Hashtbl.length collection.path_specific = 0 then acc
      else if
        (not (List.is_empty path_solutions))
        && Extraction.check_types_against_target
             (List.map (fun (_, (b : ExistentializedBlock.t)) -> b.ty) acc)
             target_type
      then acc
      else
        let enumeration_result =
          synthesis_helper target_type (current_cost + 1) collection operations
            collection_file acc
        in
        enumeration_result)

  let synthesis (target_type : rty) (max_cost : int)
      (inital_seeds : PrioritySynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list)
      (collection_file : string) : (LocalCtx.t * (t, t term) typed list) list =
    max_cost_ref := max_cost;

    print_endline "Initial seeds";
    PrioritySynthesisCollection.print inital_seeds;
    Core.Out_channel.write_all collection_file
      ~data:(PrioritySynthesisCollection.layout inital_seeds);

    let paths_finished_by_seeds =
      check_and_remove_finished_paths inital_seeds
    in

    (* TODO: With the result, we may want to minimize
       `minimize_num extracted_blocks target_ty`*)
    (if Hashtbl.length inital_seeds.path_specific = 0 then
       paths_finished_by_seeds
     else
       synthesis_helper target_type 4 inital_seeds operations collection_file
         paths_finished_by_seeds)
    |> List.map (fun (lc, b) -> (lc, ExistentializedBlock.to_typed_term b))
    |> group_by (fun (x, y) -> x)
    |> List.map (fun (x, y) -> (x, List.map snd y))
end
