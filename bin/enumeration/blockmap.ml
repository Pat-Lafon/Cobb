open Block
open Blockset
open Context
open Utils
open Typing.Termcheck

module BlockMapF (B : Block_intf) = struct
  module BlockSet = BlockSetF (B)

  type t = (Nt.t * BlockSet.t) list

  let empty : t = []

  let to_list (map : t) : B.t list =
    List.map (fun (_, s) -> BlockSet.to_list s) map |> List.flatten

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
        if Nt.eq ty ty' then (ty, BlockSet.add_block terms term) :: rest
        else (ty', terms) :: add rest term

  (** Add the (type, term pair to the map) *)
  let rec add_list (map : t) (term_list : BlockSet.t) (ty : Nt.t) : t =
    match map with
    | [] -> [ (ty, term_list) ]
    | (ty', terms) :: rest ->
        if Nt.eq ty ty' then (ty, BlockSet.union terms term_list) :: rest
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

  let layout (map : t) : string =
    let aux (ty, terms) =
      Printf.sprintf "Type: %s\n" (layout_ty ty) ^ BlockSet.layout terms
    in
    List.fold_left (fun acc x -> acc ^ aux x) "" map

  let print (map : t) : unit = print_endline (layout map)

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

  let increment_by_args (block_args : PreBlock.t Seq.t)
      (promotable_paths : LocalCtx.t list) (filter_type : _ option) :
      t * (LocalCtx.t, t) Hashtbl.t =
    let res : t * (LocalCtx.t, t) Hashtbl.t =
      Seq.fold_left
        (fun ((new_map, path_specific_list) : _ * (LocalCtx.t, t) Hashtbl.t)
             (pre_block : PreBlock.t) ->
          let (general_block, path_promo_list) :
              Block.t option * (LocalCtx.t * Block.t) list =
            apply pre_block filter_type promotable_paths
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

  let existentialized_list (map : t) (ty : Nt.t) : ExistentializedBlock.t list =
    get_opt map ty
    |> Option.map BlockSet.to_list
    |> Option.value ~default:[]
    |> List.map Block.existentialize
end
