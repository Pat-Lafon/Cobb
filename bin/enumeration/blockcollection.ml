open Blockmap
open Block

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

  let layout ({ new_blocks; old_blocks } : t) : string =
    "New Blocks:\n" ^ BlockMap.layout new_blocks ^ "Old Blocks:\n"
    ^ BlockMap.layout old_blocks

  let print (coll : t) : unit = print_endline (layout coll)

  let make_new_old ({ new_blocks; old_blocks } : t) : t =
    assert_valid { new_blocks; old_blocks };
    { new_blocks = []; old_blocks = BlockMap.union new_blocks old_blocks }

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
