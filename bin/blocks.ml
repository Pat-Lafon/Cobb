open Nt
open Typing.Termcheck
open Language.FrontendTyped
open Utils
open Pieces
open Frontend_opt.To_typectx
open Zzdatatype.Datatype
open Tracking
open Pomap
open Language
open Context
open Relation
open Block

module BlockSetF (B : Block_intf) : sig
  type t

  val empty : t
  val size : t -> int
  val singleton : B.t -> t
  val add_block : t -> B.t -> t
  val find_block_opt : t -> B.t -> B.t option
  val get_idx : t -> Ptset.elt -> B.t
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val to_list : t -> B.t list
  val print : t -> unit
  val print_ptset : t -> Ptset.t -> unit
  val is_empty : t -> bool
  val fold : ('a -> B.t -> 'a) -> 'a -> t -> 'a
  val get_succs : t -> B.t -> Ptset.t
  val get_preds : t -> B.t -> Ptset.t
end = struct
  module BlockOrdering = struct
    type el = B.t
    type ord = Unknown | Lower | Equal | Greater

    let relations_to_ord = function
      | Relations.Equiv -> Equal
      | Relations.ImpliesTarget -> Lower
      | Relations.ImpliedByTarget -> Greater
      | Relations.None -> Unknown
      | Relations.Timeout -> Unknown

    let compare (a : el) (b : el) =
      let uctx = Context.get_global_uctx () in
      B.typing_relation uctx a b |> relations_to_ord
  end

  module P = Pomap_impl.Make (BlockOrdering)

  module D =
    Display_hasse_impl.Make
      (P)
      (struct
        include Display_hasse_impl.DefaultSpec

        type el = unit
        type 'a node = 'a P.node

        let pp_node_attr (ppf : Format.formatter) (node : el node) : unit =
          Format.fprintf ppf "label = \"%s\"" (P.get_key node |> B.layout)

        let rotation = 0.
      end)

  type t = unit P.pomap

  let empty : t = P.empty
  let size (pm : t) : int = P.cardinal pm
  let is_empty (pm : t) : bool = P.is_empty pm
  let singleton (x : P.key) : t = P.singleton x ()
  let add_block (pm : t) x : t = P.add x () pm

  let find_block_opt (pm : t) (x : P.key) : P.key option =
    try Some (P.find x pm |> snd |> P.get_key) with Not_found -> None

  let get_idx (pm : t) (idx : Ptset.elt) : P.key = P.find_ix idx pm |> P.get_key

  let union (l : t) (r : t) : t =
    (* A minor optimization to choose a size order for performing a union *)
    if P.cardinal r > P.cardinal l then P.union r l else P.union l r

  let inter (l : t) (r : t) : t =
    (* A minor optimization to choose a size order for performing a inter *)
    if P.cardinal r > P.cardinal l then P.inter r l else P.inter l r

  let diff (l : t) (r : t) : t = P.diff l r
  let print (pm : t) : unit = D.printf pm

  let print_ptset (pm : t) (set : Ptset.t) : unit =
    print_endline
      ("Printing Ptset, Cardinality: " ^ string_of_int (Ptset.cardinal set));
    let new_pm = P.filter (fun idx n -> Ptset.mem idx set) pm in
    print new_pm

  let to_list (pm : t) : P.key list =
    P.fold (fun b acc -> P.get_key b :: acc) pm []

  let fold (f : 'a -> P.key -> 'a) (acc : 'a) (pm : t) : 'a =
    P.fold (fun n acc -> f acc (P.get_key n)) pm acc

  let get_succs (pm : t) (b : P.key) : Ptset.t =
    P.find b pm |> snd |> P.get_sucs

  let get_preds (pm : t) (b : P.key) : Ptset.t =
    P.find b pm |> snd |> P.get_prds
end

module BlockSetE = BlockSetF (ExistentializedBlock)

module BlockMapF (B : Block_intf) = struct
  module BlockSet = BlockSetF (B)

  type t = (Nt.t * BlockSet.t) list

  let empty : t = []

  let size (map : t) : int =
    List.fold_left (fun acc (_, set) -> acc + BlockSet.size set) 0 map

  let is_empty (map : t) : bool =
    List.for_all (fun (_, set) -> BlockSet.is_empty set) map

  let assert_valid (map : t) : unit =
    assert (
      List.for_all
        (fun (ty, set) ->
          List.find_all (fun (t, _) -> t == ty) map |> List.length = 1)
        map)

  (** Add the (type, term pair to the map) *)
  let rec add (map : t) (term : B.t) : t =
    match map with
    | [] -> [ (B.to_nty term, BlockSet.singleton term) ]
    | (ty', terms) :: rest ->
        let ty = B.to_nty term in
        if eq ty ty' then (ty, BlockSet.add_block terms term) :: rest
        else (ty', terms) :: add rest term

  (** Add the (type, term pair to the map) *)
  let rec add_list (map : t) (term_list : BlockSet.t) (ty : Nt.t) : t =
    match map with
    | [] -> [ (ty, term_list) ]
    | (ty', terms) :: rest ->
        if eq ty ty' then (ty, BlockSet.union terms term_list) :: rest
        else (ty', terms) :: add_list rest term_list ty

  let init (inital_seeds : B.t list) : t =
    let aux (b_map : t) term =
      (* layout_block term |> print_endline; *)
      add b_map term
    in
    List.fold_left aux [] inital_seeds

  let get_opt (map : t) (ty : Nt.t) : BlockSet.t option = List.assoc_opt ty map

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

  let rec _add_to_path_specifc_list (path_specific : (LocalCtx.t * t) list)
      (local_ctx : LocalCtx.t) (b : B.t) =
    match path_specific with
    | [] -> [ (local_ctx, init [ b ]) ]
    | (l, m) :: rest ->
        if l = local_ctx then (l, add m b) :: rest
        else (l, m) :: _add_to_path_specifc_list rest local_ctx b
end

module BlockMap = struct
  include BlockMapF (Block)

  module BlockSet = struct
    include BlockSet

    let existentialize (pm : t) : BlockSetE.t =
      fold
        (fun acc n -> BlockSetE.add_block acc (Block.existentialize n))
        BlockSetE.empty pm
  end

  (** Gets the corresponding set or return  *)
  let get (map : t) (ty : Nt.t) : BlockSet.t =
    get_opt map ty |> Option.value ~default:BlockSet.empty

  let add_potential_block_to_maps general_block path_promo_list new_map
      path_specific_list =
    match general_block with
    | None ->
        ( new_map,
          List.fold_left
            (fun (acc : (LocalCtx.t, t) Hashtbl.t) ((x, y) : _ * Block.t) :
                 (LocalCtx.t, t) Hashtbl.t ->
              match Hashtbl.find_opt acc x with
              | None ->
                  Hashtbl.replace acc x (init [ y ]);
                  acc
              | Some s ->
                  Hashtbl.replace acc x (add s y);
                  acc)
            path_specific_list path_promo_list )
    | Some s ->
        assert (List.is_empty path_promo_list);
        (add new_map s, path_specific_list)

  let new_old_block_args (new_blocks : t) (old_blocks : t) (args : Nt.t list) :
      Block.t list Seq.t =
    range (List.length args)
    |> superset |> List.to_seq
    |> Seq.flat_map (fun new_set ->
           (* Loop from 0 to args.len - 1 to choose an index for the `new_blocks` *)
           List.mapi
             (fun j ty : Block.t list ->
               if List.mem j new_set then get new_blocks ty |> BlockSet.to_list
               else get old_blocks ty |> BlockSet.to_list)
             args
           |> n_cartesian_product |> List.to_seq)

  let req_req_args (required_blocks : t) (required_blocks2 : t)
      (optional_blocks : t) (args : Nt.t list) : Block.t list Seq.t =
    let n = List.length args in
    arg_coloring n |> List.to_seq
    |> Seq.flat_map (fun l : Block.t list Seq.t ->
           List.mapi
             (fun idx choice : Block.t list ->
               let ty = List.nth args idx in
               match choice with
               | Some true -> get required_blocks ty |> BlockSet.to_list
               | Some false -> get required_blocks2 ty |> BlockSet.to_list
               | None -> get optional_blocks ty |> BlockSet.to_list)
             l
           |> n_cartesian_product |> List.to_seq)

  let increment_by_args (block_args : Block.t list Seq.t)
      ((component, (args, ret_type)) : Pieces.component * (Nt.t list * Nt.t))
      (promotable_paths : LocalCtx.t list) (filter_type : _ option) :
      t * (LocalCtx.t, t) Hashtbl.t =
    let res : t * (LocalCtx.t, t) Hashtbl.t =
      Seq.fold_left
        (fun ((new_map, path_specific_list) : _ * (LocalCtx.t, t) Hashtbl.t)
             (args : Block.t list) ->
          let (general_block, path_promo_list)
                : Block.t option * (LocalCtx.t * Block.t) list =
            apply component args ret_type filter_type promotable_paths
          in
          add_potential_block_to_maps general_block path_promo_list new_map
            path_specific_list)
        (empty, Hashtbl.create 5)
        block_args
    in
    print_endline "Finished increment";
    assert_valid (fst res);
    Hashtbl.iter (fun l m -> assert_valid m) (snd res);
    res
end

module BlockCollection = struct
  (* Blocks are added to the `new_blocks` field *)
  (* `new_blocks` get shifted over to `old_blocks` when we increment to a new, larger set of blocks *)
  type t = { new_blocks : BlockMap.t; old_blocks : BlockMap.t }

  (** Initialize a block collection with the given seeds values
    * Seeds are initial blocks that are just variables, constants, or operations that take no arguments (or just unit) *)
  let init (inital_seeds : Block.t list) : t =
    let new_blocks : BlockMap.t = BlockMap.init inital_seeds in
    { new_blocks; old_blocks = [] }

  let assert_valid ({ new_blocks; old_blocks } : t) : unit =
    BlockMap.assert_valid new_blocks;
    BlockMap.assert_valid old_blocks

  let print ({ new_blocks; old_blocks } : t) : unit =
    Printf.printf "New Blocks:\n";
    BlockMap.print new_blocks;
    Printf.printf "Old Blocks:\n";
    BlockMap.print old_blocks

  let make_new_old ({ new_blocks; old_blocks } : t) : t =
    assert_valid { new_blocks; old_blocks };
    { new_blocks = []; old_blocks = BlockMap.union new_blocks old_blocks }

  (** For the block inference
    * Returns a mapping of all blocks, new and old *)
  let get_full_map ({ new_blocks; old_blocks } : t) : BlockMap.t =
    BlockMap.union new_blocks old_blocks

  let rec add_map_with_cov_checked coll (map : BlockMap.t) =
    BlockMap.assert_valid map;
    match map with
    | [] -> coll
    | (ty, set) :: rest ->
        let ({ new_blocks; old_blocks } : t) =
          add_map_with_cov_checked coll rest
        in
        let new_set = BlockMap.BlockSet.diff set (BlockMap.get old_blocks ty) in
        { new_blocks = BlockMap.add_list new_blocks new_set ty; old_blocks }
end

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

  let print ({ general_coll; path_specific } : t) : unit =
    Printf.printf "General Collection:\n";
    BlockCollection.print general_coll;
    Printf.printf "Path Specific Collection:\n";

    Hashtbl.to_seq path_specific
    |> Seq.iter (fun (local_ctx, block_collection) ->
           layout_typectx layout_rty local_ctx |> print_endline;
           BlockCollection.print general_coll)

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
                else ();

                (* This is the standard approach by looking at new path blocks *)
                let standard_args =
                  BlockMap.new_old_block_args path_col.new_blocks set_of_args
                    nt_args
                in

                let args =
                  if List.length nt_args = 1 then standard_args
                  else
                    (* Alternatively, look at new general blocks with old stuff *)
                    let alternative_args =
                      BlockMap.req_req_args
                        (* First required set is the new general blocks*)
                        general_new_blocks
                        (* Second required is the path_blocks *)
                        (BlockMap.union path_col.new_blocks path_col.old_blocks)
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
  let unioned_rty_type (l : (LocalCtx.t * (identifier * t rty) * Ptset.t) list)
      : t rty =
    List.map (fun (_, (_, rt), _) -> rt) l |> union_rtys

  (* Helper function to get the current rty of terms under consideration *)
  let unioned_rty_type2
      (l : (LocalCtx.t * BlockSetE.t * (identifier * t rty) * Ptset.t) list) :
      t rty =
    assert (not (List.is_empty l));
    List.map (fun (_, _, (_, rt), _) -> rt) l |> union_rtys

  (* Try to find the largest block that can be removed *)
  let minimize_once
      (x : (LocalCtx.t * BlockSetE.t * (identifier * t rty) * Ptset.t) list)
      (target_ty : t rty) :
      (LocalCtx.t * BlockSetE.t * (identifier * t rty) * Ptset.t) list =
    if List.length x = 1 then x
    else
      let () = assert (List.length x > 1) in

      let uctx = !global_uctx |> Option.get in

      print_endline (layout_rty target_ty);

      (* Assert that current min passes subtyping check *)
      assert (sub_rty_bool uctx (unioned_rty_type2 x, target_ty));

      let current_min = unioned_rty_type2 x in

      print_endline (unioned_rty_type2 x |> layout_rty);

      let res =
        List.fold_left
          (fun (current_min, current_list) proposed_list ->
            let proposed_min = unioned_rty_type2 proposed_list in
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

      assert (sub_rty_bool uctx (unioned_rty_type2 res, target_ty));
      res

  (* Repeat trying to reduce the number of blocks until minimum is found *)
  let minimize_num
      (x : (LocalCtx.t * BlockSetE.t * ExistentializedBlock.t * Ptset.t) list)
      (target_ty : t rty) :
      (LocalCtx.t * BlockSetE.t * ExistentializedBlock.t * Ptset.t) list =
    let rec aux (x : _ list) =
      let new_x = minimize_once x target_ty in
      if List.length new_x < List.length x then aux new_x else new_x
    in
    aux x

  let rec minimize_type_helper (lc : LocalCtx.t) (map : BlockSetE.t)
      (target_ty : t rty) (acc : 'a list) (remaining_set : Ptset.t)
      (current_minimum : t rty) : (t rty * 'a list) option =
    if Ptset.is_empty remaining_set then None
    else
      let idx = Ptset.choose remaining_set in
      let remaining_set = Ptset.remove idx remaining_set in
      let new_term = BlockSetE.get_idx map idx in
      let id, rty = new_term in

      let new_thing : LocalCtx.t * BlockSetE.t * (identifier * t rty) * Ptset.t
          =
        (lc, map, (id, rty), BlockSetE.get_preds map new_term)
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
      (target_ty : t rty) :
      (LocalCtx.t * BlockSetE.t * ExistentializedBlock.t * Ptset.t) list =
    let uctx = !global_uctx |> Option.get in
    let current_coverage_type = unioned_rty_type2 x in
    assert (sub_rty_bool uctx (current_coverage_type, target_ty));

    let res =
      List.fold_left
        (fun (current_min_coverage, (acc : _ list)) (idx : int) :
             (t rty * _ list) ->
          let current_term, rest_terms =
            Core.List.drop x idx |> List.destruct_opt |> Option.get
          in

          let lc, map, (_, _), ptset = current_term in

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

  (* Try to increase the coverage of a specific term to satisfy
     the target type *)
  let setup_type (x : (LocalCtx.t * BlockSetE.t * ('a option * Ptset.t)) list)
      (target_ty : t rty) :
      (LocalCtx.t * BlockSetE.t * (identifier * t rty) * Ptset.t) list =
    print_endline "Setup type";
    assert (not (List.is_empty x));
    let uctx = !global_uctx |> Option.get in

    (* print_endline (layout_rty target_ty); *)
    let res =
      List.map
        (fun (lc, map, (current_block, under_set)) ->
          match current_block with
          | Some i ->
              let id, rty = i in
              print_endline "This block";
              [ (lc, map, (id, rty), under_set) ]
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
                under_set [])
        x
      |> List.concat
    in

    assert (sub_rty_bool uctx (unioned_rty_type2 res, target_ty));
    res

  (* Take blocks of different coverage types and join them together into full programs using non-deterministic choice *)
  let extract_blocks (collection : SynthesisCollection.t) (target_ty : t rty) :
      (LocalCtx.t * ExistentializedBlock.t) list =
    let target_nty = erase_rty target_ty in

    (* Create a target block that we are missing *)
    let target_block : ExistentializedBlock.t =
      ( (Rename.unique "missing") #: target_nty |> NameTracking.known_var,
        target_ty )
    in

    print_endline "Existentializing the general set";
    (* Get all blocks from the general collection *)
    let general_block_list =
      BlockCollection.get_full_map collection.general_coll |> fun x ->
      BlockMap.get x target_nty |> BlockSet.to_list
      |> List.map Block.existentialize
    in

    let uctx = Context.get_global_uctx () in

    (* The updated set is commented out because we don't to include the target
       block in later calculations *)
    let equal_block =
      List.find_opt
        (fun b ->
          match ExistentializedBlock.typing_relation uctx b target_block with
          | Relations.Equiv -> true
          | _ -> false)
        general_block_list
    in

    assert (Hashtbl.length collection.path_specific > 0);

    match equal_block with
    | Some b ->
        print_endline "Handling the equal_block case";
        let current : _ =
          Hashtbl.fold
            (fun lc _ acc ->
              (* We already have our solution so we only need the set of paths *)
              ( lc,
                BlockSetE.empty,
                ExistentializedBlock.path_promotion lc b,
                Ptset.empty )
              :: acc)
            collection.path_specific []
        in

        let current = minimize_num current target_ty in

        List.map (fun (lc, _, b, _) -> (lc, b)) current
    | _ -> (
        print_endline "Existentializing the path specific sets";
        Relations.clear_cache ();

        (* Get the sets for each path *)
        let path_specific_sets =
          Hashtbl.map
            (fun (lc, bc) ->
              LocalCtx.layout lc |> print_endline;
              ( lc,
                BlockCollection.get_full_map bc |> fun x ->
                BlockMap.get_opt x target_nty
                |> Option.map BlockSet.to_list
                |> Option.value ~default:[]
                |> List.map Block.existentialize ))
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

              let conditional_add (bs : BlockSetE.t)
                  (b : ExistentializedBlock.t) : BlockSetE.t =
                if ExistentializedBlock.is_sub_rty uctx b path_target_ty then
                  BlockSetE.add_block bs b
                else if ExistentializedBlock.is_sub_rty uctx path_target_ty b
                then BlockSetE.add_block bs b
                else bs
              in

              (* Fold over general_terms for this path and path promote them *)
              let res =
                List.fold_left
                  (fun acc b ->
                    conditional_add acc
                      (ExistentializedBlock.path_promotion lc b))
                  res general_block_list
              in

              (* Fold over path specific terms for this path *)
              let res =
                List.fold_left
                  (fun acc b -> conditional_add acc b)
                  res path_blocks
              in

              (lc, res))
            path_specific_sets
        in

        Printf.printf "\n\n Path Specific collections we are interested in\n";
        Hashtbl.iter
          (fun ctx set ->
            let path_target_ty =
              ExistentializedBlock.path_promotion ctx target_block
            in
            let set = BlockSetE.add_block set path_target_ty in
            Printf.printf "Path Specific Collection: %s\n"
              (layout_typectx layout_rty ctx);
            BlockSetE.print set)
          path_specific_sets;

        print_endline "ready to match";

        (* We have one check that a component covers the full target *)
        (* TODO: May have been made redundant/not worth the complexity*)
        match
          Hashtbl.to_seq path_specific_sets
          |> Seq.find_map (fun (lc, path_set) ->
                 BlockSetE.find_block_opt path_set target_block
                 |> Option.map (fun b -> (lc, b)))
          (* List.find_map
             (fun (lc, path_set) ->
               BlockSetE.find_block_opt path_set target_block
               |> Option.map (fun b -> (lc, b)))
             path_specific_sets *)
        with
        | Some s ->
            print_endline "In the case where we have a match";
            (* print_endline (layout_typectx layout_rty lc);
               print_endline (Block.layout b);
               print_endline "We just shortcircuit in this case"; *)
            [ s ]
        | _ ->
            print_endline "In other case";

            let block_options_in_each_path :
                (LocalCtx.t * BlockSetE.t * ('a option * Ptset.t)) list =
              Hashtbl.fold
                (fun lc set acc ->
                  let path_target_block =
                    ExistentializedBlock.path_promotion lc target_block
                  in

                  ExistentializedBlock.layout path_target_block |> print_endline;

                  (* Does the target exist in this path? *)
                  match BlockSetE.find_block_opt set path_target_block with
                  | Some b ->
                      (* Yes: Return current bs, no preds, and the target_block *)
                      print_endline "Have a complete block for a path solution";
                      (lc, set, (Some b, Ptset.empty)) :: acc
                  | None ->
                      (* No: Return a new bs with the target block, any preds, and
                         possibly a starting block from the succs *)
                      let bs = BlockSetE.add_block set path_target_block in
                      let p = BlockSetE.get_preds bs path_target_block in
                      let s = BlockSetE.get_succs bs path_target_block in
                      BlockSetE.print_ptset bs p;

                      (* Smallest block that covers the target fully *)
                      let b =
                        Ptset.min_elt_opt s
                        |> Option.map (fun idx -> BlockSetE.get_idx bs idx)
                      in

                      (print_endline "Have a partial solution: ";
                       match b with
                       | Some b -> print_endline (ExistentializedBlock.layout b)
                       | None -> print_endline "None");

                      (* Some paths might not get blocks that aid in getting the
                         target? *)
                      if not (Ptset.is_empty p && Ptset.is_empty s) then (
                        print_endline "return a block";
                        (lc, bs, (b, p)) :: acc)
                      else (
                        print_endline "return nothing";
                        acc))
                path_specific_sets []
            in

            print_endline
              ("Num_starting_choices: "
              ^ string_of_int (List.length block_options_in_each_path));

            let block_choices =
              setup_type block_options_in_each_path target_ty
            in

            Pp.printf "Target Type: %s\n" (layout_rty target_ty);
            Pp.printf "Current Type: %s\n"
              (layout_rty (unioned_rty_type2 block_choices));
            List.iter
              (fun (lc, _, b, _) ->
                Pp.printf "Local Context: %s\n" (layout_typectx layout_rty lc);
                Pp.printf "Block:\n%s\n" (ExistentializedBlock.layout b))
              block_choices;

            let block_choices = minimize_type block_choices target_ty in

            Pp.printf "Improved Type: %s\n"
              (layout_rty (unioned_rty_type2 block_choices));
            List.iter
              (fun (lc, _, b, _) ->
                Pp.printf "Local Context: %s\n" (layout_typectx layout_rty lc);
                Pp.printf "Block:\n%s\n" (ExistentializedBlock.layout b))
              block_choices;

            let block_choices = minimize_num block_choices target_ty in

            (* When we are done, drop any remaining predesessors and the block
               map *)
            List.map (fun (lc, _, b, _) -> (lc, b)) block_choices)
end

module Synthesis = struct
  let rec synthesis_helper (max_depth : int) (target_type : t rty)
      (collection : SynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list) :
      (LocalCtx.t * _ list) list =
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
          operations

  (** Given some initial setup, run the synthesis algorithm *)
  let synthesis (target_type : t rty) (max_depth : int)
      (inital_seeds : SynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list) :
      (LocalCtx.t * _) list =
    (* SynthesisCollection.print inital_seeds; *)
    synthesis_helper max_depth target_type inital_seeds operations
end
