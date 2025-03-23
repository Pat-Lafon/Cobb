open Pomap
open Context

(* open Relation *)
open Block
open Blockset
open Blockmap

(* open Blockcollection *)
open Utils
open Zzdatatype.Datatype
open Language.FrontendTyped
open Typing.Termcheck

(* open Synthesiscollection *)
open Frontend_opt.To_typectx
open Language

type rty = Nt.t Language.rty

module Extraction = struct
  module BlockSet = BlockMap.BlockSet

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
  let unioned_rty_type2
      (l : (LocalCtx.t * BlockSetE.t * ExistentializedBlock.t * Ptset.t) list) :
      rty =
    assert (not (List.is_empty l));
    List.map (fun (_, _, ({ ty; _ } : ExistentializedBlock.t), _) -> ty) l
    |> union_rtys

  (* Helper function to get the current rty of terms under consideration *)
  let unioned_rty_type3 (l : (LocalCtx.t * ExistentializedBlock.t) list) : rty =
    assert (not (List.is_empty l));
    List.map (fun (_, ({ ty; _ } : ExistentializedBlock.t)) -> ty) l
    |> union_rtys

  (* Try to find the largest block that can be removed *)
  let minimize_once (x : (LocalCtx.t * ExistentializedBlock.t) list)
      (target_ty : rty) : (LocalCtx.t * ExistentializedBlock.t) list =
    if List.length x = 1 then x
    else
      let () = assert (List.length x > 1) in

      let uctx = !global_uctx |> Option.get in

      print_endline (layout_rty target_ty);

      let current_min = unioned_rty_type3 x in

      (* Assert that current min passes subtyping check *)
      assert (sub_rty_bool uctx (current_min, target_ty));

      print_endline (current_min |> layout_rty);

      let res =
        List.fold_left
          (fun (current_min, current_list) proposed_list ->
            let proposed_min = unioned_rty_type3 proposed_list in
            if
              (* The proposed min implies the target*)
              sub_rty_bool uctx (proposed_min, target_ty)
              &&
              (* And it is implied by the current min*)
              sub_rty_bool uctx (current_min, proposed_min)
            then (proposed_min, proposed_list)
            else (current_min, current_list))
          (current_min, x)
          (combnk (List.length x - 1) x)
        |> snd
      in

      assert (sub_rty_bool uctx (unioned_rty_type3 res, target_ty));
      res

  (* Repeat trying to reduce the number of blocks until minimum is found *)
  let minimize_num (x : (LocalCtx.t * ExistentializedBlock.t) list)
      (target_ty : rty) : (LocalCtx.t * ExistentializedBlock.t) list =
    let rec aux (x : _ list) =
      let new_x = minimize_once x target_ty in
      if List.length new_x < List.length x then aux new_x else new_x
    in
    aux x

  let rec minimize_type_helper (lc : LocalCtx.t) (map : BlockSetE.t)
      (target_ty : rty) (acc : 'a list) (remaining_set : Ptset.t)
      (current_minimum : rty) : (rty * 'a list) option =
    if Ptset.is_empty remaining_set then None
    else
      let idx = Ptset.choose remaining_set in
      let remaining_set = Ptset.remove idx remaining_set in
      let new_term = BlockSetE.get_idx map idx in

      (*       let id, rty = new_term in *)
      let new_thing :
          LocalCtx.t * BlockSetE.t * ExistentializedBlock.t * Ptset.t =
        (lc, map, new_term, BlockSetE.get_preds map new_term)
      in

      let new_covered_rty = unioned_rty_type2 (new_thing :: acc) in

      let uctx = !global_uctx |> Option.get in

      if sub_rty_bool uctx (new_covered_rty, target_ty) then
        if sub_rty_bool uctx (current_minimum, new_covered_rty) then
          Some (new_covered_rty, new_thing :: acc)
        else
          minimize_type_helper lc map target_ty acc remaining_set
            current_minimum
      else
        (* Other successors to draw on if not sufficient in hitting the target
           type *)
        minimize_type_helper lc map target_ty (new_thing :: acc) remaining_set
          current_minimum

  (* Try to reduce coverage of a specific term*)
  let minimize_type
      (x : (LocalCtx.t * BlockSetE.t * ExistentializedBlock.t * Ptset.t) list)
      (target_ty : rty) :
      (LocalCtx.t * BlockSetE.t * ExistentializedBlock.t * Ptset.t) list =
    let uctx = !global_uctx |> Option.get in
    let current_coverage_type = unioned_rty_type2 x in
    assert (sub_rty_bool uctx (current_coverage_type, target_ty));

    let res =
      List.fold_left
        (fun (current_min_coverage, (acc : _ list)) (idx : int) : (rty * _ list)
           ->
          let current_term, rest_terms =
            Core.List.drop x idx |> List.destruct_opt |> Option.get
          in

          let lc, map, _, ptset = current_term in

          if Ptset.is_empty ptset then
            (* Bail out if there are no other possible options*)
            ( current_min_coverage,
              (* List.concat [ acc; [ current_term ]; rest_terms ]  *)
              current_term :: acc )
          else
            match
              minimize_type_helper lc map target_ty
                (List.concat [ acc; rest_terms ])
                ptset current_min_coverage
            with
            | None -> (current_min_coverage, current_term :: acc)
            | Some x -> x)
        (current_coverage_type, [])
        (range (List.length x))
      |> snd
    in
    assert (sub_rty_bool uctx (unioned_rty_type2 res, target_ty));
    res

  let check_types_against_target (tys : t Rty.rty list) (target_ty : t Rty.rty)
      : bool =
    let uctx = !global_uctx |> Option.get in
    sub_rty_bool uctx (union_rtys tys, target_ty)

  let pset_is_sufficient_coverage (map : BlockSetE.t) (pset : Ptset.t)
      (target_ty : rty) : bool =
    let block_candidates =
      Ptset.fold
        (fun idx acc ->
          let b = BlockSetE.get_idx map idx in
          print_endline "current block";
          ExistentializedBlock.layout b |> print_endline;
          b.ty :: acc)
        pset []
    in
    if List.is_empty block_candidates then false
    else check_types_against_target block_candidates target_ty

  (* Try to increase the coverage of a specific term to satisfy
     the target type *)
  let setup_type
      ((lc, map, (current_block, under_set)) :
        LocalCtx.t * BlockSetE.t * (ExistentializedBlock.t option * Ptset.t))
      (target_ty : rty) :
      (LocalCtx.t * BlockSetE.t * ExistentializedBlock.t * Ptset.t) list =
    print_endline "Setup type";
    let uctx = !global_uctx |> Option.get in

    (* print_endline (layout_rty target_ty); *)
    let res =
      match current_block with
      | Some i ->
          print_endline "This block";
          [ (lc, map, i, under_set) ]
      | None ->
          Ptset.fold
            (fun idx acc ->
              let b = BlockSetE.get_idx map idx in
              let p = BlockSetE.get_preds map b in
              print_endline "current block";
              ExistentializedBlock.layout b |> print_endline;

              print_endline "Printing Preds";
              BlockSetE.print_ptset map p;
              (lc, map, b, p) :: acc)
            under_set []
    in

    assert (not (List.is_empty res));

    if not (sub_rty_bool uctx (unioned_rty_type2 res, target_ty)) then (
      List.iter
        (fun (lc, _, eb, _) ->
          LocalCtx.layout lc |> print_endline;
          ExistentializedBlock.layout eb |> print_endline)
        res;

      failwith "Setup_type does not have enough");
    res

  (** Lets try and simplify the extraction process by only considering one path
      at a time *)
  let extract_precise_blocks_for_path (lc : LocalCtx.t)
      (target_path_block : ExistentializedBlock.t) (bset : BlockSetE.t) :
      (LocalCtx.t * ExistentializedBlock.t) list =
    Printf.printf
      "\n\n Extracting from path-specific collections we are interested in\n";

    print_endline "Target block";
    ExistentializedBlock.layout target_path_block |> print_endline;

    (* (let set = BlockSetE.add_block bset target_path_block in
       Printf.printf "Path Specific Collection: %s\n"
         (layout_typectx layout_rty lc);
       BlockSetE.print set); *)

    (* Does the target exist in this path? *)
    match BlockSetE.find_block_opt bset target_path_block with
    | Some b ->
        (* Yes: Return current bs, no preds, and the target_block *)
        print_endline "Have a complete block for a path solution";
        (lc, b) :: []
    | None ->
        print_endline "No solution from this path";
        []
  (* (* No: Return a new bs with the target block, any preds, and
        possibly a starting block from the succs *)
     let bs = BlockSetE.add_block bset target_path_block in
     let p = BlockSetE.get_preds bs target_path_block in
     let s = BlockSetE.get_succs bs target_path_block in
     BlockSetE.print_ptset bs p;

     (* Smallest block that covers the target fully *)
     (* let b =
          Ptset.min_elt_opt s
          |> Option.map (fun idx -> BlockSetE.get_idx bs idx)
        in

        (print_endline "Have a partial solution: ";
         match b with
         | Some b -> print_endline (ExistentializedBlock.layout b)
         | None -> print_endline "None"); *)
     (* TODO, we are going to avoid blocks that are too large for the moment *)
     let b = None in

     (* Some paths might not get blocks that aid in getting the
        target? *)
     if not (Ptset.is_empty p && Ptset.is_empty s) then
       if
         Option.is_none b
         && not (pset_is_sufficient_coverage bs p target_path_block.ty)
       then (
         print_endline "return nothing2";
         [])
       else (
         print_endline "return a block";
         let starting_point = (lc, bs, (b, p)) in

         let target_path_ty = target_path_block.ty in

         let block_choices = setup_type starting_point target_path_ty in

         let block_choices = minimize_type block_choices target_path_ty in

         Pp.printf "Improved Type: %s\n"
           (layout_rty (unioned_rty_type2 block_choices));
         List.iter
           (fun (lc, _, b, _) ->
             Pp.printf "Local Context: %s\n" (layout_typectx layout_rty lc);
             Pp.printf "Block:\n%s\n" (ExistentializedBlock.layout b))
           block_choices;

         let block_choices =
           List.map (fun (lc, _, b, _) -> (lc, b)) block_choices
         in

         let block_choices = minimize_num block_choices target_path_ty in

         (* When we are done, drop any remaining predesessors and the block
            map *)
         block_choices)
     else (
       print_endline "return nothing";
       []) *)

  (** Lets try and simplify the extraction process by only considering one path
      at a time *)
  let extract_for_path (lc : LocalCtx.t)
      (target_path_block : ExistentializedBlock.t) (bset : BlockSetE.t) :
      (LocalCtx.t * ExistentializedBlock.t) list =
    Printf.printf
      "\n\n Extracting from path-specific collections we are interested in\n";

    print_endline "Target block";
    ExistentializedBlock.layout target_path_block |> print_endline;

    (let set = BlockSetE.add_block bset target_path_block in
     Printf.printf "Path Specific Collection: %s\n"
       (layout_typectx layout_rty lc);
     BlockSetE.print set);

    (* Does the target exist in this path? *)
    match BlockSetE.add_or_find bset target_path_block with
    | Found b ->
        (* Yes: Return current bs, no preds, and the target_block *)
        print_endline "Have a complete block for a path solution";
        (lc, b) :: []
    | Added bset ->
        (* No: Return a new bs with the target block, any preds, and
           possibly a starting block from the succs *)
        (*         let starting_len = BlockSetE.size bset in

        let bs = BlockSetE.add_block bset target_path_block in
        (*  assert (starting_len < BlockSetE.size bs); *)

        print_endline "lol"; *)
        BlockSetE.print bset;

        let p = BlockSetE.get_preds bset target_path_block in
        let s = BlockSetE.get_succs bset target_path_block in
        BlockSetE.print_ptset bset p;

        (* Smallest block that covers the target fully *)
        (* let b =
             Ptset.min_elt_opt s
             |> Option.map (fun idx -> BlockSetE.get_idx bs idx)
           in

           (print_endline "Have a partial solution: ";
            match b with
            | Some b -> print_endline (ExistentializedBlock.layout b)
            | None -> print_endline "None"); *)
        (* TODO, we are going to avoid blocks that are too large for the moment *)
        let b = None in

        (* Some paths might not get blocks that aid in getting the
           target? *)
        if not (Ptset.is_empty p && Ptset.is_empty s) then
          if
            Option.is_none b
            && not (pset_is_sufficient_coverage bset p target_path_block.ty)
          then (
            print_endline "return nothing2";
            [])
          else (
            print_endline "return a block";
            let starting_point = (lc, bset, (b, p)) in

            let target_path_ty = target_path_block.ty in

            let block_choices = setup_type starting_point target_path_ty in

            let block_choices = minimize_type block_choices target_path_ty in

            Pp.printf "Improved Type: %s\n"
              (layout_rty (unioned_rty_type2 block_choices));
            List.iter
              (fun (lc, _, b, _) ->
                Pp.printf "Local Context: %s\n" (layout_typectx layout_rty lc);
                Pp.printf "Block:\n%s\n" (ExistentializedBlock.layout b))
              block_choices;

            let block_choices =
              List.map (fun (lc, _, b, _) -> (lc, b)) block_choices
            in

            let block_choices = minimize_num block_choices target_path_ty in

            (* When we are done, drop any remaining predesessors and the block
               map *)
            block_choices)
        else (
          print_endline "return nothing";
          [])

  (* Take blocks of different coverage types and join them together into full programs using non-deterministic choice *)
  (* let extract_blocks (collection : SynthesisCollection.t) (target_ty : rty) :
      (LocalCtx.t * ExistentializedBlock.t) list =
    let target_nty = erase_rty target_ty in

    let target_block : ExistentializedBlock.t =
      ExistentializedBlock.create_target target_ty
    in

    print_endline "Existentializing the general set";
    (* Get all blocks from the general collection *)
    let general_block_list =
      let ({ new_blocks; old_blocks } : BlockCollection.t) =
        collection.general_coll
      in

      List.append
        (BlockMap.existentialized_list new_blocks target_nty)
        (BlockMap.existentialized_list old_blocks target_nty)
    in

    let uctx = Context.get_global_uctx () in

    assert (Hashtbl.length collection.path_specific > 0);

    print_endline "Existentializing the path specific sets";
    Relations.clear_cache ();

    (* Get the sets for each path *)
    let path_specific_sets =
      Hashtbl.map
        (fun (lc, bc) ->
          LocalCtx.layout lc |> print_endline;
          ( lc,
            let ({ new_blocks; old_blocks } : BlockCollection.t) = bc in

            List.append
              (BlockMap.existentialized_list new_blocks target_nty)
              (BlockMap.existentialized_list old_blocks target_nty) ))
        collection.path_specific
    in

    (* We are going to do some normalization setup *)
    (* All General terms are going to get pushed into paths *)
    let path_specific_sets =
      Hashtbl.map
        (fun ((lc : LocalCtx.t), (path_blocks : _ list)) ->
          let res = BlockSetE.empty in
          (* TODO: We should only use this block once and enable caching *)
          (* Existentialization should rename the block... Maybe still worth
             it to clear cache lol just to not flood things*)
          let path_target_ty =
            ExistentializedBlock.path_promotion lc target_block
          in

          let conditional_add (bs : BlockSetE.t) (b : ExistentializedBlock.t) :
              BlockSetE.t =
            if ExistentializedBlock.is_sub_rty uctx b path_target_ty then
              BlockSetE.add_block bs b
            else if ExistentializedBlock.is_sub_rty uctx path_target_ty b then
              BlockSetE.add_block bs b
            else bs
          in

          (* Fold over general_terms for this path and path promote them *)
          let res =
            List.fold_left
              (fun acc b ->
                conditional_add acc (ExistentializedBlock.path_promotion lc b))
              res general_block_list
          in

          (* Fold over path specific terms for this path *)
          let res =
            List.fold_left (fun acc b -> conditional_add acc b) res path_blocks
          in

          (lc, (path_target_ty, res)))
        path_specific_sets
    in

    Printf.printf "\n\n Path Specific collections we are interested in\n";
    Hashtbl.iter
      (fun ctx (path_target_ty, set) ->
        let set = BlockSetE.add_block set path_target_ty in
        Printf.printf "Path Specific Collection: %s\n"
          (layout_typectx layout_rty ctx);
        BlockSetE.print set)
      path_specific_sets;

    let path_specific_sets_list =
      Hashtbl.to_seq path_specific_sets |> List.of_seq
    in

    let extracted_blocks =
      List.fold_left
        (fun acc (lc, (target_path_ty, set)) ->
          List.append acc (extract_for_path lc target_path_ty set))
        [] path_specific_sets_list
    in

    minimize_num extracted_blocks target_ty *)
end
