open Language.FrontendTyped
open Utils
open Pieces
open Zzdatatype.Datatype
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
  let nty_target_type = Rty.erase_rty target_type in
  PrioritySynthesisCollection.fold_by_type collection nty_target_type 0
    (fun acc bset -> acc + BlockSet.size bset)

module PrioritySynthesis = struct
  let rec synthesis_helper (target_type : rty) (current_cost : int)
      (*      (priority_queue : PathPriorityQueue.t) *)
        (collection : PrioritySynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list)
      (collection_file : string) (acc : (LocalCtx.t * _) list) :
      (LocalCtx.t * _) list =
    if !max_cost_ref < current_cost then failwith "Max cost exceeded"
    else print_endline "Current Collection";

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
      enumeration_result

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
       (* let priority_queue : PathPriorityQueue.t =
            PathPriorityQueue.init
              (Hashtbl.to_seq_keys inital_seeds.path_specific |> Seq.length)
          in *)
       synthesis_helper target_type 4 (* priority_queue *) inital_seeds
         operations collection_file paths_finished_by_seeds)
    |> List.map (fun (lc, b) -> (lc, ExistentializedBlock.to_typed_term b))
    |> group_by (fun (x, y) -> x)
    |> List.map (fun (x, y) -> (x, List.map snd y))
end

(* module Synthesis = struct
  let rec synthesis_helper (max_depth : int) (target_type : rty)
      (collection : SynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list)
      (collection_file : string) : (LocalCtx.t * _ list) list =
    print_endline "Current Collection";
    SynthesisCollection.print collection;
    Core.Out_channel.write_all collection_file
      ~data:(SynthesisCollection.layout collection);

    match max_depth with
    | 0 ->
        print_endline "Starting Extraction";
        (*        failwith (string_of_int !Backend.Check.query_counter); *)
        Extraction.extract_blocks collection target_type
        |> List.map (fun (lc, b) -> (lc, ExistentializedBlock.to_typed_term b))
        |> group_by (fun (x, y) -> x)
    | depth ->
        print_endline ("Enumeration Depth(in reverse): " ^ string_of_int depth);
        let operations =
          if depth == 1 then
            let nty = erase_rty target_type in
            List.filter (fun (p, (_, ret_ty)) -> ret_ty = nty) operations
          else operations
        in
        let optional_filter_type =
          if depth == 1 then Some target_type else None
        in
        (* If not, increment the collection and try again *)
        synthesis_helper (depth - 1) target_type
          (SynthesisCollection.increment collection operations
             optional_filter_type)
          operations collection_file

  (** Given some initial setup, run the synthesis algorithm *)
  let synthesis (target_type : rty) (max_depth : int)
      (inital_seeds : SynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list)
      (collection_file : string) : (LocalCtx.t * _) list =
    (* SynthesisCollection.print inital_seeds; *)
    synthesis_helper max_depth target_type inital_seeds operations
      collection_file
end *)
