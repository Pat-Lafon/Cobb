open Typing
open Nt
open Typing.Termcheck
open Language.FrontendTyped
open Utils
open Pieces
open Frontend_opt.To_typectx
open Zzdatatype.Datatype
open Timeout
open Tracking
open Pomap
open Language

let global_uctx : uctx option ref = ref None

type local_ctx = t rty Typectx.ctx

(* Combining to local contexts together for renaming *)
let local_ctx_union_r (Typectx l : local_ctx) (r : local_ctx) :
    local_ctx * (string, string) Hashtbl.t =
  map_fst
    (fun (Typectx.Typectx res) ->
      (* TODO: Duplicates *)
      Typectx.Typectx (l @ res))
    (NameTracking.freshen r)

let uctx_add_local_ctx (uctx : uctx) (ctx : local_ctx) : uctx =
  {
    uctx with
    local_ctx =
      Typectx
        (List.concat [ Typectx.to_list ctx; Typectx.to_list uctx.local_ctx ]);
  }

let promote_ctx_to_path local_ctx ~promote_ctx =
  Typectx.Typectx (Typectx.to_list local_ctx @ Typectx.to_list promote_ctx)

let combine_all_args args =
  let arg_names = List.map (fun (id, _, _) -> id) args in
  let ctxs = List.map (fun (_, _, ctx) -> ctx) args in
  let unchanged_arg_name = List.hd arg_names in
  let unchanged_context = List.hd ctxs in
  List.fold_left2
    (fun ((args : identifier list), (acc_context : local_ctx)) (id : identifier)
         changed_ctx : (identifier list * local_ctx) ->
      let new_ctx, mapping = local_ctx_union_r acc_context changed_ctx in
      ( args
        @ [
            (match Hashtbl.find_opt mapping id.x with
            | Some s -> s
            | None ->
                Printf.printf "id: %s\n" id.x;
                List.iter (fun id -> Printf.printf "%s\n" id.x) args;
                Hashtbl.iter (fun k v -> Printf.printf "%s -> %s\n" k v) mapping;
                List.iter
                  (fun l -> layout_typectx layout_rty l |> print_endline)
                  ctxs;
                failwith "you messed up")
            #: id.ty;
          ],
        new_ctx ))
    ([ unchanged_arg_name ], unchanged_context)
    (List.tl arg_names) (List.tl ctxs)

type subtypingres = NoOverlap | NotSubset | Res of (t rty, t rty term) typed

let analyze_subtyping_result (new_rty : (t rty, t rty term) typed option) :
    subtypingres =
  match new_rty with
  | Some new_rty -> (
      match new_rty.ty with
      | RtyBase { cty = Cty { phi = Lit { x = AC (B false); _ }; _ }; _ } ->
          NoOverlap
      | _ -> Res new_rty)
  | None -> NotSubset

module Block = struct
  type t = identifier * Nt.t rty * local_ctx

  (* TODO: pretty print blocks as just expressions? *)
  (* let pprint_block_as_exp ((_name, _ut, _ctx) : block) : string =
     failwith "pretty_print_blocks::unimplemented" *)

  let layout ((name, ut, ctx) : t) : string =
    Printf.sprintf "%s\n⊢ %s: %s :\n%s\n"
      (layout_typectx layout_rty ctx ^ " ")
      (Pieces.ast_to_string name)
      (layout_ty name.ty) (layout_rty ut)
end

module rec RelationCache : sig
  val add : identifier -> identifier -> Relations.relation -> unit
  val check : identifier -> identifier -> Relations.relation option
end = struct
  type t = (string * string, Relations.relation) Hashtbl.t

  let cache : t = Hashtbl.create 10000

  let add (l : identifier) (r : identifier) (rel : Relations.relation) : unit =
    Hashtbl.add cache (l.x, r.x) rel

  let check (l : identifier) (r : identifier) : Relations.relation option =
    match Hashtbl.find_opt cache (l.x, r.x) with
    | Some r -> Some r
    | None ->
        Hashtbl.find_opt cache (r.x, l.x)
        |> Option.map Relations.invert_relation
end

and Relations : sig
  type relation = Equiv | ImpliesTarget | ImpliedByTarget | None | Timeout

  val sexp_of_relation : relation -> Core.Sexp.t
  val is_equiv_or_timeout : relation -> bool
  val rty_typing_relation : uctx -> t rty -> t rty -> relation
  val block_typing_relation : uctx -> Block.t -> Block.t -> relation
  val invert_relation : relation -> relation
end = struct
  type relation = Equiv | ImpliesTarget | ImpliedByTarget | None | Timeout
  [@@deriving sexp]

  let invert_relation = function
    | Equiv -> Equiv
    | ImpliesTarget -> ImpliedByTarget
    | ImpliedByTarget -> ImpliesTarget
    | None -> None
    | Timeout -> Timeout

  let is_equiv_or_timeout (r : relation) : bool =
    match r with Equiv | Timeout -> true | _ -> false

  let diff_base_type (l : t rty) (r : t rty) : bool =
    not (erase_rty l = erase_rty r)

  let rty_typing_relation ctx target_ty ty =
    if diff_base_type target_ty ty then None
    else
      let implies_target =
        Timeout.sub_rty_bool_or_timeout ctx (ty, target_ty)
      in

      (* Short circuit on timeout *)
      if implies_target = Timeout then Timeout
      else
        (* Else continue *)
        let implied_by_target =
          Timeout.sub_rty_bool_or_timeout ctx (target_ty, ty)
        in
        match (implies_target, implied_by_target) with
        | Timeout, _ | _, Timeout -> Timeout
        | Result true, Result true -> Equiv
        | Result true, _ -> ImpliesTarget
        | _, Result true -> ImpliedByTarget
        | _ -> None

  let block_typing_relation (uctx : uctx) (target_block : Block.t)
      (block : Block.t) =
    let target_id, target_ty, target_ctx = target_block in
    let id, ty, ctx = block in

    match RelationCache.check target_id id with
    | Some r -> r
    | None ->
        let res =
          if diff_base_type target_ty ty then None
          else
            let combined_ctx, mapping = local_ctx_union_r target_ctx ctx in
            let updated_ty = Pieces.ut_subst ty mapping in

            rty_typing_relation
              (uctx_add_local_ctx uctx combined_ctx)
              target_ty updated_ty
        in
        RelationCache.add target_id id res;
        res
end

module BlockSet : sig
  type t

  val empty : t
  val singleton : Block.t -> t
  val add_block : t -> Block.t -> t
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val to_list : t -> Block.t list
  val print : t -> unit
  val is_empty : t -> bool
  val extract : t -> Block.t -> Block.t option * Ptset.t * Ptset.t
end = struct
  module P = Pomap_impl.Make (struct
    type el = Block.t
    type ord = Unknown | Lower | Equal | Greater

    let relations_to_ord = function
      | Relations.Equiv -> Equal
      | Relations.ImpliesTarget -> Lower
      | Relations.ImpliedByTarget -> Greater
      | Relations.None -> Unknown
      | Relations.Timeout -> Unknown

    let compare (a : el) (b : el) =
      let uctx = !global_uctx |> Option.get in
      Relations.block_typing_relation uctx a b |> relations_to_ord
  end)

  module D =
    Display_hasse_impl.Make
      (P)
      (struct
        include Display_hasse_impl.DefaultSpec

        type el = unit
        type 'a node = 'a P.node

        let pp_node_attr (ppf : Format.formatter) (node : el node) : unit =
          Format.fprintf ppf "label = \"%s\"" (P.get_key node |> Block.layout)

        let rotation = 0.
      end)

  type t = unit P.pomap

  let empty : t = P.empty
  let is_empty (pm : t) : bool = P.is_empty pm
  let singleton (x : Block.t) : t = P.singleton x ()
  let add_block (pm : t) x : t = P.add x () pm
  let union (l : t) (r : t) : t = P.union l r
  let inter (l : t) (r : t) : t = P.inter l r
  let diff (l : t) (r : t) : t = P.diff l r
  let print (pm : t) : unit = D.printf pm

  let to_list (pm : t) : P.key list =
    P.Store.fold (fun b acc -> P.get_key b :: acc) (P.get_nodes pm) []

  let extract (pm : t) (b : P.key) =
    let equal_block, n, pm =
      match P.add_find b () pm with
      | Found (_, n) ->
          print_endline "found";
          (Some (P.get_key n), n, pm)
      | Added (_, n, new_pm) ->
          print_endline "added";
          (None, n, new_pm)
    in

    print_endline "extracting for pm";
    print pm;

    let pred_blocks = P.get_prds n in
    let succ_blocks = P.get_sucs n in
    (equal_block, pred_blocks, succ_blocks)
end

module BlockMap = struct
  type t = (Nt.t * BlockSet.t) list

  let empty : t = []

  let is_empty (map : t) : bool =
    List.for_all (fun (_, set) -> BlockSet.is_empty set) map

  (** Add the (type, term pair to the map) *)
  let rec add (map : t) (term : Block.t) (ty : Nt.t) : t =
    match map with
    | [] -> [ (ty, BlockSet.singleton term) ]
    | (ty', terms) :: rest ->
        if eq ty ty' then (ty, BlockSet.add_block terms term) :: rest
        else (ty', terms) :: add rest term ty

  (** Add the (type, term pair to the map) *)
  let rec add_list (map : t) (term_list : BlockSet.t) (ty : Nt.t) : t =
    match map with
    | [] -> [ (ty, term_list) ]
    | (ty', terms) :: rest ->
        if eq ty ty' then (ty, BlockSet.union terms term_list) :: rest
        else (ty', terms) :: add_list rest term_list ty

  let init (inital_seeds : (Block.t * Nt.t) list) : t =
    let aux (b_map : t) (term, ty) =
      (* layout_block term |> print_endline; *)
      add b_map term ty
    in
    List.fold_left aux [] inital_seeds

  let get_opt (map : t) (ty : Nt.t) : BlockSet.t option = List.assoc_opt ty map

  (** Gets the corresponding set or return  *)
  let get (map : t) (ty : Nt.t) : BlockSet.t =
    get_opt map ty |> Option.value ~default:BlockSet.empty

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

  let check_coverage_with_args uctx block_id new_ut arg_names : bool =
    List.exists
      (fun ({ x; _ } as id : identifier) ->
        (*                    let joined_uctx = uctx_add_local_ctx uctx joined_ctx in *)
        let arg_t = FrontendTyped.get_opt uctx x |> Option.get in
        let relation_result =
          Relations.rty_typing_relation uctx arg_t new_ut.ty
        in
        let () = RelationCache.add id block_id relation_result in
        Relations.is_equiv_or_timeout relation_result)
      arg_names

  let rec _add_to_path_specifc_list (path_specific : (local_ctx * t) list)
      (local_ctx : local_ctx) (b : Block.t) ret_type =
    match path_specific with
    | [] -> [ (local_ctx, init [ (b, ret_type) ]) ]
    | (l, m) :: rest ->
        if l = local_ctx then (l, add m b ret_type) :: rest
        else (l, m) :: _add_to_path_specifc_list rest local_ctx b ret_type

  (* Promotable_paths should be empty if the new_blocks comes form a
       specific path *)
  (* Returns a block map for the new blocks... plus optionally a block map of
     those promoted to a new path *)
  (* Should we separate out the general and path specific cases? *)
  let increment (new_blocks : t) (old_blocks : t)
      ((component, (args, ret_type)) : Pieces.component * (Nt.t list * Nt.t))
      (promotable_paths : local_ctx list) : t * (local_ctx * t) list =
    let uctx = !global_uctx |> Option.get in

    (* Loop from 0 to args.len - 1 to choose an index for the `new_blocks` *)
    List.fold_left
      (fun acc new_set ->
        let l =
          List.mapi
            (fun j ty : Block.t list ->
              if List.mem j new_set then get new_blocks ty |> BlockSet.to_list
              else get old_blocks ty |> BlockSet.to_list)
            args
          |> n_cartesian_product
        in

        List.fold_left
          (fun (new_map, path_specific_list) (args : Block.t list) ->
            (* Correct joining of contexts? *)
            let (arg_names : identifier list), (joined_ctx : local_ctx) =
              combine_all_args args
            in

            let block_id, term = Pieces.apply component arg_names in

            let new_uctx : uctx = uctx_add_local_ctx uctx joined_ctx in

            assert (term.ty = block_id.ty);

            let new_ut =
              Termcheck.term_type_infer_with_rec_check new_uctx
                { x = term.x; ty = block_id.ty }
            in

            match analyze_subtyping_result new_ut with
            | NoOverlap -> (new_map, path_specific_list)
            | NotSubset ->
                (* failed the new rec_check *)
                ( new_map,
                  (List.fold_left
                     (fun path_specific_list x ->
                       let new_path_ctx =
                         promote_ctx_to_path new_uctx.local_ctx ~promote_ctx:x
                       in

                       let new_path_uctx =
                         { new_uctx with local_ctx = new_path_ctx }
                       in
                       let new_path_ut =
                         Termcheck.term_type_infer_with_rec_check new_path_uctx
                           { x = term.x; ty = block_id.ty }
                       in
                       match analyze_subtyping_result new_path_ut with
                       | Res new_ut ->
                           let new_path_ctx =
                             Typectx.add_to_right new_path_ctx
                               { x = block_id.x; ty = new_ut.ty }
                           in
                           _add_to_path_specifc_list path_specific_list x
                             (block_id, new_ut.ty, new_path_ctx)
                             ret_type
                       | _ -> path_specific_list)
                     path_specific_list)
                    promotable_paths )
            | Res new_ut ->
                (* Check if new term is coverage equivalent to one of it's
                   arguments *)
                if check_coverage_with_args new_uctx block_id new_ut arg_names
                then (* Ignore term if so *)
                  (new_map, path_specific_list)
                else
                  let new_ctx =
                    Typectx.add_to_right joined_ctx
                      { x = block_id.x; ty = new_ut.ty }
                  in
                  ( add new_map (block_id, new_ut.ty, new_ctx) ret_type,
                    path_specific_list ))
          acc l)
      (empty, [])
      (range (List.length args) |> superset)
end

module BlockCollection = struct
  (* Blocks are added to the `new_blocks` field *)
  (* `new_blocks` get shifted over to `old_blocks` when we increment to a new, larger set of blocks *)
  type t = { new_blocks : BlockMap.t; old_blocks : BlockMap.t }

  (** Initialize a block collection with the given seeds values
    * Seeds are initial blocks that are just variables, constants, or operations that take no arguments (or just unit) *)
  let init (inital_seeds : (Block.t * Nt.t) list) : t =
    let new_blocks : BlockMap.t = BlockMap.init inital_seeds in
    { new_blocks; old_blocks = [] }

  let print ({ new_blocks; old_blocks } : t) : unit =
    Printf.printf "New Blocks:\n";
    BlockMap.print new_blocks;
    Printf.printf "Old Blocks:\n";
    BlockMap.print old_blocks

  let make_new_old ({ new_blocks; old_blocks } : t) : t =
    { new_blocks = []; old_blocks = BlockMap.union new_blocks old_blocks }

  (** For the block inference
    * Returns a mapping of all blocks, new and old *)
  let get_full_map ({ new_blocks; old_blocks } : t) : BlockMap.t =
    BlockMap.union new_blocks old_blocks

  let rec add_map_with_cov_checked coll (map : BlockMap.t) =
    match map with
    | [] -> coll
    | (ty, set) :: rest ->
        let { new_blocks; old_blocks } : t =
          add_map_with_cov_checked coll rest
        in
        assert (not (List.mem_assoc ty new_blocks));
        let old_set = BlockMap.get old_blocks ty in
        let new_set = BlockSet.diff set old_set in
        { new_blocks = (ty, new_set) :: new_blocks; old_blocks }
end

module SynthesisCollection = struct
  type t = {
    general_coll : BlockCollection.t;
    path_specific : (local_ctx * BlockCollection.t) list;
  }
  (** A set of block_collections, a general one and some path specific ones *)

  let init (inital_seeds : BlockMap.t)
      (path_specific_seeds : (local_ctx * BlockMap.t) list) : t =
    let general_coll : BlockCollection.t =
      { new_blocks = inital_seeds; old_blocks = [] }
    in
    let path_specific =
      List.map
        (fun (ctx, seeds) : (_ * BlockCollection.t) ->
          (ctx, { new_blocks = seeds; old_blocks = [] }))
        path_specific_seeds
    in
    { general_coll; path_specific }

  let print ({ general_coll; path_specific } : t) : unit =
    Printf.printf "General Collection:\n";
    BlockCollection.print general_coll;
    Printf.printf "Path Specific Collection:\n";
    List.iter
      (fun (local_ctx, block_collection) ->
        layout_typectx layout_rty local_ctx |> print_endline;
        BlockCollection.print general_coll)
      path_specific

  (* First list must be a superset of the second in terms of local_ctx used*)
  let merge_path_specific_maps
      (path_specific : (local_ctx * BlockCollection.t) list)
      (path_specific_maps : (local_ctx * BlockMap.t) list) :
      (local_ctx * BlockCollection.t) list =
    assert (List.length path_specific >= List.length path_specific_maps);
    List.map
      (fun (l, bc) ->
        match List.assoc_opt l path_specific_maps with
        | Some b -> (l, BlockCollection.add_map_with_cov_checked bc b)
        | None -> (l, bc))
      path_specific

  let increment (collection : t)
      (operations : (Pieces.component * (Nt.t list * Nt.t)) list) : t =
    (* We want to support the normal block_collection_increment as normal *)
    (* We want to be able to increment using new_seeds and old_seeds +
       old_general_seeds for path specific variations *)
    (* Still want to check for equivalence *)
    let general_new_blocks = collection.general_coll.new_blocks in
    let general_old_blocks = collection.general_coll.old_blocks in
    let promotable_paths = List.map fst collection.path_specific in
    let path_specific_block_collections = collection.path_specific in

    let new_collection =
      {
        general_coll = BlockCollection.make_new_old collection.general_coll;
        path_specific =
          List.map
            (fun (ctx, path_specific_collection) ->
              (ctx, BlockCollection.make_new_old path_specific_collection))
            path_specific_block_collections;
      }
    in

    let new_collection =
      (* Iterate over all components *)
      List.fold_left
        (fun { general_coll; path_specific } op ->
          (* Iterate over sets of possible new maps *)
          let new_map, path_specific_maps =
            BlockMap.increment general_new_blocks general_old_blocks op
              promotable_paths
          in

          {
            general_coll =
              BlockCollection.add_map_with_cov_checked general_coll new_map;
            path_specific =
              merge_path_specific_maps path_specific path_specific_maps;
          })
        new_collection operations
    in

    let path_specific_maps =
      List.fold_left
        (fun acc (local_ctx, (path_col : BlockCollection.t)) ->
          let path_specific_map =
            List.fold_left
              (fun acc op ->
                let path_op_specific_map, promoted_blocks =
                  BlockMap.increment path_col.new_blocks
                    (BlockMap.union path_col.old_blocks general_old_blocks)
                    op []
                in
                assert (List.is_empty promoted_blocks);
                BlockMap.union acc path_op_specific_map)
              (BlockMap.init []) operations
          in
          if BlockMap.is_empty path_specific_map then acc
          else (local_ctx, path_specific_map) :: acc)
        [] path_specific_block_collections
    in

    {
      new_collection with
      path_specific =
        merge_path_specific_maps new_collection.path_specific path_specific_maps;
    }
end

module Synthesis = struct
  type program = (t, t term) Mtyped.typed

  (* Take blocks of different coverage types and join them together into full programs using non-deterministic choice *)
  let under_blocks_join (collection : SynthesisCollection.t) (target_ty : t rty)
      : program option =
    let target_nty = erase_rty target_ty in
    let uctx = !global_uctx |> Option.get in

    (* Create a target block that we are missing *)
    let target_block : Block.t =
      ( (Rename.unique "missing") #: target_nty |> NameTracking.known_var,
        target_ty,
        uctx.local_ctx )
    in

    (* Get all blocks from the collection *)
    let general_set =
      BlockCollection.get_full_map collection.general_coll |> fun x ->
      BlockMap.get x target_nty
    in
    (* Get all blocks from the collection *)
    Printf.printf "\n\n Generall collection we are interested in\n";
    BlockSet.print general_set;

    let path_specific_sets =
      List.filter_map
        (fun (lc, bc) ->
          BlockCollection.get_full_map bc |> fun x ->
          BlockMap.get_opt x target_nty |> Option.map (fun x -> (lc, x)))
        collection.path_specific
    in

    Printf.printf "\n\n Path Specific collections we are interested in\n";
    List.iter
      (fun (ctx, set) ->
        Printf.printf "Path Specific Collection\n";
        BlockSet.print set)
      path_specific_sets;

    let block_options_generally = BlockSet.extract general_set target_block in

    let block_options_in_each_path =
      List.map
        (fun (lc, bs) -> (lc, BlockSet.extract bs target_block))
        path_specific_sets
    in


    (* Do we care about pred blocks from general?
       Pred blocks have less coverage than the target
       Hmmm, maybe starting from smallest and going up?
       Except when you already have no coverage from paths... then skip straight
       to the succ_blocks since you need all the coverage
        Not true because you can join small blocks together
       *)
    let (equal_block, _pred_blocks, succ_blocks) = block_options_generally in
    match equal_block with
    | Some (b) ->
        print_endline (Block.layout b);
        failwith "Can we just short circuit the general case and finish?"
    | _ -> ();


    (match
       List.find_opt
         (fun (_, (eq, _, _)) -> Option.is_some eq)
         block_options_in_each_path
     with
    | Some (lc, (Some b, _, _)) ->
        print_endline (layout_typectx layout_rty lc);
        print_endline (Block.layout b);
        failwith "Can we just short circuit and finish in this case?"
    | _ -> ());

    if List.is_empty block_options_in_each_path then
      failwith "todo"
    else failwith "continue"

    (* Need to existentialized : exists_rtys_to_rty *)
    (* Need to union together : union_rtys *)

    (* What are we interested in here? *)
    (* We have general terms and path specific terms *)
    (* General terms can be promoted to be path specific *)
    (* let new_path_ctx =
                       promote_ctx_to_path new_uctx.local_ctx ~promote_ctx:x
                     in *)
    (* When does this promotion need to happen? *)
    (* We want need the actual target_ty, the missing coverage, not the overall
       spec *)
    (* What do we need for that? Ideally incorporate Zhe's work... especially
       since it is now apparently fast *)
    (* I want to factor out the promote block to path logic from incrememnt *)
    (* I want to look for three things, types that imply my target, types that
       equal my target and are implied by my target *)
    (* Equal terms might mean we are done... though some will need to be
       promoted *)
    (* When does repair happen? Now? Or do I extract this out? *)
    (* We want to run one final check over the completed program *)

    (* let groups =
         group_by
           (fun (_id, ut, ctx) ->
             (* Blocks.layout_block (id, ut, ctx) |> print_endline; *)
             (* print_endline "\n\nNew candidate";
                Blocks.mmt_type_to_string ut |> print_endline;
                List.iter
                  (fun (id, mmt) ->
                    print_string (id ^ ": ");
                    print_endline (Blocks.mmt_type_to_string mmt);
                    print_endline (Pieces.ast_to_string ~erased:true id))
                  ctx;
                print_string ((id : id NNtyped.typed).x ^ ": ");
                Pieces.ast_to_string ~erased:true (id : id NNtyped.typed).x
                |> print_endline; *)
             (* subtyping_check __FILE__ __LINE__ uctx
                (MMT.UtNormal (UT.make_basic_bot (snd body.NL.ty)))
                ty *)
             let x = Blocks.uctx_add_local_ctx uctx ctx in
             Relations.rty_typing_relation x target_ty ut)
           u_b_list
       in *)

    (* let _ =
         List.iter
           (fun ((g, es) : Relations.relation * Blocks.block_set) ->
             print_string "Group ";
             print_endline (Core.Sexp.to_string_hum (Relations.sexp_of_relation g));
             List.iter
               (fun b ->
                 Blocks.layout_block b |> print_endline
                 (* Pp.printf "%s: %s : %s\n" id.x
                    (Pieces.ast_to_string ~erased:true id)
                    (layout_rty rty) *))
               es)
           groups
       in *)
    (* let super_type_list =
         List.find_map
           (fun (g, es) -> if g == Relations.ImpliesTarget then Some es else None)
           groups
         |> Option.get
       in
       let sub_type_list =
         List.find_map
           (fun (g, es) ->
             if g == Relations.ImpliedByTarget then Some es else None)
           groups
         |> Option.get
       in *)

    (* let potential_program =
         if List.length super_type_list > 0 then
           let potential_program = List.hd super_type_list in
           (* We will check all of the other super_types to see if there is a program
              that is smaller but still works *)
           let potential_program =
             List.fold_left
               (fun p e ->
                 let r = Relations.block_typing_relation uctx p e in

                 (* If the new block is smaller then use it *)
                 if r == Relations.ImpliedByTarget then e else p)
               potential_program (List.tl super_type_list)
           in
           Some potential_program
         else None
       in *)

  let rec synthesis_helper (max_depth : int) (target_type : t rty)
      (collection : SynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list) : program option =
    match max_depth with
    | 0 ->
        SynthesisCollection.print collection;
        (* Join blocks together into programs *)
        under_blocks_join collection target_type
    | depth ->
        let operations =
          if depth == 1 then
            let nty = erase_rty target_type in
            List.filter
              (fun (p, (_, ret_ty)) ->
                let res = ret_ty = nty in
                print_endline
                  (Pieces.layout_component p ^ " " ^ string_of_bool res);
                res)
              operations
          else operations
        in
        (* If not, increment the collection and try again *)
        synthesis_helper (depth - 1) target_type
          (SynthesisCollection.increment collection operations)
          operations

  (** Given some initial setup, run the synthesis algorithm *)
  let synthesis (target_type : t rty) (max_depth : int)
      (inital_seeds : SynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list) : program option =
    SynthesisCollection.print inital_seeds;
    synthesis_helper max_depth target_type inital_seeds operations
end

(* let%test "bot_int" =
  let ty = Ty_int in
  let t = term_bot ty in
  is_base_bot t *)
