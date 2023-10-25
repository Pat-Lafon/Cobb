open Typecheck
open Underctx
open Languages
open Underty.T
open Normalty.Ast.NT
open Autov.Prop
open Config
open Assertion
open Sugar
open Languages.StrucNA

(** Produces a list from 0..n-1*)
let range n = List.init n (fun x -> x)

(** Takes a list and performs a *)
let rec n_cartesian_product = function
  | [] -> [ [] ]
  | x :: xs ->
      let rest = n_cartesian_product xs in
      List.concat (List.map (fun i -> List.map (fun rs -> i :: rs) rest) x)

let%test "should fail" = 2 + 2 = 5
let%test "range" = range 5 = [0;1;2;3;4]

module Blocks = struct
  type base_type = Ntyped.t
  type block = NL.term NNtyped.typed

  (* bool -> var1, true
     int -> 0, 1, ...*)
  type block_map = (base_type * block list) list

  (* Blocks are added to the `new_blocks` field *)
  (* `new_blocks` get shifted over to `old_blocks` when we increment to a new, larger set of blocks *)
  type block_collection = { new_blocks : block_map; old_blocks : block_map }

  (** Enforces uniqueness of the inner block list*)
  let rec block_list_add (lst : block list) (term : block) : block list =
    match lst with
    | [] -> [ term ]
    | hd :: tl ->
        if hd = term then failwith "term is not unique in block list"
        else hd :: block_list_add tl term

  (** Add the (type, term pair to the map)*)
  let rec block_map_add (map : block_map) (term : block) (ty : base_type) :
      block_map =
    match map with
    | [] -> [ (ty, [ term ]) ]
    | (ty', terms) :: rest ->
        if ty = ty' then (ty, block_list_add terms term) :: rest
        else (ty', terms) :: block_map_add rest term ty

  let rec block_map_get (map : block_map) (ty : base_type) : block list =
    match map with
    | [] -> []
    | (ty', terms) :: rest -> if ty = ty' then terms else block_map_get rest ty

  let block_map_init (inital_seeds : (base_type * block) list) : block_map =
    let aux (b_map : block_map) (ty, term) = block_map_add b_map term ty in

    List.fold_left aux [] inital_seeds

  (** Initialize a block collection with the given seeds values
    * Seeds are initial blocks that are just variables, constants, or operations that take no arguments (or just unit) *)
  let block_collection_init (inital_seeds : (base_type * block) list) :
      block_collection =
    let new_blocks : block_map = block_map_init inital_seeds in
    { new_blocks; old_blocks = [] }

  (** For the block inference
    * Returns a mapping of all blocks, new and old *)
  let rec block_collection_get_full_map
      ({ new_blocks; old_blocks } : block_collection) : block_map =
    match new_blocks with
    | [] -> old_blocks
    | (ty, terms) :: rest ->
        let old_terms = block_map_get old_blocks ty in
        let new_terms = List.concat [ old_terms; terms ] in
        (ty, new_terms)
        :: block_collection_get_full_map { new_blocks = rest; old_blocks }

  (** Given a collection, we want to construct a new set of blocks using some set of operations
    * Operations should not be valid seeds (i.e. must be operations that take arguments)*)
  let block_collection_increment (collection : block_collection)
      (operations : (unit * base_type list * base_type) list) : block_collection
      =
    (* We pull aside our current `new_blocks`, these are the largest blocks in the collection *)
    let new_blocks = collection.new_blocks in
    (* New and old blocks get merged together *)
    (* These will make up the old blocks of the next collection *)
    let old_blocks = block_collection_get_full_map collection in

    (* For each operation in the list, we are going to iterate though it's argument types and pull out blocks that match said types *)
    (* Atleast one arguement use to create each new block must be from `new_blocks`, the rest are from `old_blocks`(which can also have blocks from `new_blocks`). This guarantees that all created blocks are of `new_blocks[i].size + 1` *)
    let resulting_blocks : (base_type * block) list =
      (* Loop over each of the operations*)
      List.map
        (fun (_, args, ret_type) : (base_type * block) list ->
          (* Loop from 0 to args.len - 1 to choose an index for the `new_blocks`*)
          List.map
            (fun i ->
              (* Loop over each of the arguments, getting a list of blocks for each one *)
              let l =
                List.mapi
                  (fun j ty : block list ->
                    if i == j then block_map_get new_blocks ty
                    else block_map_get old_blocks ty)
                  args
              in
              let l = n_cartesian_product l in

              List.map
                (fun (_ : block list) : (base_type * block) ->
                  ( ret_type,
                    failwith
                      "todo, function to construct new block from args for \
                       this op" ))
                l)
            (range (List.length args))
          |> List.flatten)
        operations
      |> List.flatten
    in

    (* *)
    let new_map = block_map_init resulting_blocks in

    { new_blocks = new_map; old_blocks = new_blocks }
end

let under_ty_to_base_ty (ty : UT.t) : Blocks.base_type =
  match ty with
  | UnderTy_base { basename : id; normalty : normalty; prop : P.t } -> normalty
  | UnderTy_under_arrow _ -> failwith "not a base type"
  | UnderTy_over_arrow _ -> failwith "not a base type"
  | UnderTy_tuple _ -> failwith "not a base type"

module Synthesis = struct
  type program = NL.term NNtyped.typed
  (* int| P -> prog *)

  (** Given a block list of the appropriate type, run inference on all of them to pair them with their appropriate underapproximate types *)
  let blocks_list_infer (b_list : Blocks.block list) (uctx : uctx) :
      (UT.t * Blocks.block) list =
    (* TODO: Can this panic? What happens if type inference fails and how do we handle it?*)
    b_list
    |> List.map (fun b -> (Typecheck.Undercheck.term_type_infer uctx b, b))

  (* Take blocks of different coverage types and join them together into full programs using non-deterministic choice *)
  let under_blocks_join (u_b_list : (UT.t * Blocks.block) list) : program list =
    (* How do we want to combine blocks together? *)
    (* Maybe we also need to pass in the target UT.t type of the signature*)
    failwith "unimplemented"

  let rec synthesis_helper (max_depth : int) (target_type : UT.t) (uctx : uctx)
      (collection : Blocks.block_collection)
      (operations : (unit * Blocks.base_type list * Blocks.base_type) list) :
      program option =
    match max_depth with
    | 0 -> None
    | depth -> (
        (* Get all blocks from the collection*)
        let block_map = Blocks.block_collection_get_full_map collection in
        let base_type = under_ty_to_base_ty target_type in
        let blocks = Blocks.block_map_get block_map base_type in
        (* Infer the types of all blocks*)
        let blocks_typed = blocks_list_infer blocks uctx in
        (* Join blocks together into programs*)
        let programs = under_blocks_join blocks_typed in
        (* Check if any of the programs satisfy the target type*)
        match List.find_opt (fun p -> failwith "unimplemented") programs with
        | Some p -> Some p
        | None ->
            (* If not, increment the collection and try again*)
            synthesis_helper (depth - 1) target_type uctx
              (Blocks.block_collection_increment collection operations)
              operations)

  (** Given some initial setup, run the synthesis algorithm *)
  let synthesis (uctx : uctx) (target_type : UT.t) (max_depth : int)
      (inital_seeds : (Blocks.base_type * Blocks.block) list)
      (operations : (unit * Blocks.base_type list * Blocks.base_type) list) :
      program option =
    let init_collection = Blocks.block_collection_init inital_seeds in
    synthesis_helper max_depth target_type uctx init_collection operations
end
