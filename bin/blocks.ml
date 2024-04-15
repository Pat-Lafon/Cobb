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
open Localctx

let global_uctx : uctx option ref = ref None

type subtypingres = NoOverlap | NotSubset | Res of (t rty, t rty term) typed

let analyze_subtyping_result (new_rty : (t rty, t rty term) typed option) :
    subtypingres =
  match new_rty with
  | Some new_rty -> if rty_is_false new_rty.ty then NoOverlap else Res new_rty
  | None -> NotSubset

module Relations : sig
  type relation = Equiv | ImpliesTarget | ImpliedByTarget | None | Timeout

  val layout : relation -> string
  val invert_relation : relation -> relation
  val is_equiv_or_timeout : relation -> bool
  val diff_base_type : t rty -> t rty -> bool

  (* todo: comment this line out so everyone needs to use cache *)
  val typing_relation : uctx -> t rty -> t rty -> relation

  val typed_relation :
    uctx -> (t rty, string) typed -> (t rty, string) typed -> relation

  val check_cache : string -> string -> relation option
  val clear_cache : unit -> unit
end = struct
  type relation = Equiv | ImpliesTarget | ImpliedByTarget | None | Timeout
  [@@deriving sexp]

  let layout relation = Core.Sexp.to_string_hum (sexp_of_relation relation)

  let invert_relation = function
    | Equiv -> Equiv
    | ImpliesTarget -> ImpliedByTarget
    | ImpliedByTarget -> ImpliesTarget
    | None -> None
    | Timeout -> Timeout

  module RelationCache = struct
    type t = (string * string, relation) Hashtbl.t

    let cache : t = Hashtbl.create 10000
    let reset_cache () = Hashtbl.clear cache

    let add (l : string) (r : string) (rel : relation) : unit =
      Hashtbl.add cache (l, r) rel

    let check (l : string) (r : string) : relation option =
      match Hashtbl.find_opt cache (l, r) with
      | Some r -> Some r
      | None -> Hashtbl.find_opt cache (r, l) |> Option.map invert_relation
  end

  let is_equiv_or_timeout (r : relation) : bool =
    match r with Equiv | Timeout -> true | _ -> false

  let diff_base_type (l : t rty) (r : t rty) : bool =
    not (erase_rty l = erase_rty r)

  let check_cache = RelationCache.check
  let clear_cache () = RelationCache.reset_cache ()

  let typing_relation ctx target_ty ty =
    if diff_base_type target_ty ty then None
    else
      let implies_target =
        Timeout.sub_rty_bool_or_timeout ctx (ty, target_ty)
      in

      (* (* Short circuit on timeout *)
         if implies_target = Timeout then Timeout
         else *)
      (* Else continue *)
      let implied_by_target =
        Timeout.sub_rty_bool_or_timeout ctx (target_ty, ty)
      in
      match (implies_target, implied_by_target) with
      (*       | Timeout, _ | _, Timeout -> Timeout *)
      | Result true, Result true -> Equiv
      | Result true, _ -> ImpliesTarget
      | _, Result true -> ImpliedByTarget
      | _ -> None

  let typed_relation ctx target_id id =
    match check_cache target_id.x id.x with
    | Some r -> r
    | None ->
        let target_ty = target_id.ty in
        let ty = id.ty in
        let res = typing_relation ctx target_ty ty in
        RelationCache.add target_id.x id.x res;
        res
end

module type Block_intf = sig
  type t

  val layout : t -> string
  val to_typed_term : t -> (Nt.t, Nt.t term) typed
  val get_local_ctx : t -> LocalCtx.t
  val typing_relation : uctx -> t -> t -> Relations.relation
  val combine_all_args : t list -> identifier list * LocalCtx.t
  val path_promotion : LocalCtx.t -> t -> t
end

module ExistentializedBlock : sig
  type t = identifier * Nt.t rty

  include Block_intf with type t := t
end = struct
  type t = identifier * Nt.t rty

  let to_typed_term ((name, ut) : t) : (Nt.t, Nt.t term) typed =
    NameTracking.get_term name

  let layout ((name, ut) : t) : string =
    Printf.sprintf "%s : %s :\n%s\n"
      (NameTracking.get_term name |> layout_typed_erased_term)
      (layout_ty name.ty) (layout_rty ut)

  (* In the case of an existentialized block, the only thing in context is itself*)
  let get_local_ctx ((name, ext_rty) : t) : LocalCtx.t =
    Typectx.Typectx [ name.x #: ext_rty ]

  let new_X (x : identifier) (ty : Nt.t rty) : t = (x, ty)

  let typing_relation (uctx : uctx) ((name, ext_rty) : t)
      ((name', ext_rty') : t) : Relations.relation =
    Relations.typed_relation uctx name.x #: ext_rty name'.x #: ext_rty'

  let combine_all_args (args : t list) : identifier list * LocalCtx.t =
    failwith "unimplemented"

  let path_promotion (lc : LocalCtx.t) ((id, rt) : t) : t =
    let fresh_id = (Rename.unique id.x) #: id.ty in
    NameTracking.add_ast fresh_id (NameTracking.get_ast id |> Option.get);
    let fresh_rty = LocalCtx.exists_rtys_to_rty lc rt in

    assert (fresh_rty != rt);

    (fresh_id, fresh_rty)
end

module Block : sig
  type t = identifier * Nt.t rty * LocalCtx.t

  include Block_intf with type t := t

  val existentialize : t -> ExistentializedBlock.t
end = struct
  type t = identifier * Nt.t rty * LocalCtx.t

  let to_typed_term ((name, ut, ctx) : t) : (Nt.t, Nt.t term) typed =
    NameTracking.get_term name

  let layout ((name, ut, ctx) : t) : string =
    Printf.sprintf "%s ⊢ %s : %s :\n%s\n"
      (layout_typectx layout_rty ctx
      ^ if List.is_empty (Typectx.to_list ctx) then "" else " \n")
      (NameTracking.get_term name |> layout_typed_erased_term)
      (layout_ty name.ty) (layout_rty ut)

  let get_local_ctx ((name, ut, ctx) : t) : LocalCtx.t = ctx

  let typing_relation (uctx : uctx) (target_block : t) (block : t) :
      Relations.relation =
    let target_id, target_ty, target_ctx = target_block in
    let id, ty, ctx = block in

    let combined_ctx, mapping = LocalCtx.local_ctx_union_r target_ctx ctx in
    let updated_ty = Pieces.ut_subst ty mapping in

    Relations.typing_relation
      (LocalCtx.uctx_add_local_ctx uctx combined_ctx)
      target_ty updated_ty

  (* Takes vars with their own locals variables and constructs a list of
     arguments with a singular local context *)
  let combine_all_args (args : t list) : identifier list * LocalCtx.t =
    let arg_names = List.map (fun (id, _, _) -> id) args in
    let ctxs = List.map (fun (_, _, ctx) -> ctx) args in
    let unchanged_arg_name = List.hd arg_names in
    let unchanged_context = List.hd ctxs in
    List.fold_left2
      (fun ((args : identifier list), (acc_context : LocalCtx.t))
           (id : identifier) changed_ctx : (identifier list * LocalCtx.t) ->
        let new_ctx, mapping =
          LocalCtx.local_ctx_union_r acc_context changed_ctx
        in
        ( args
          @ [
              (match Hashtbl.find_opt mapping id.x with
              | Some s -> s
              | None ->
                  Printf.printf "id: %s\n" id.x;
                  List.iter (fun id -> Printf.printf "%s\n" id.x) args;
                  Hashtbl.iter
                    (fun k v -> Printf.printf "%s -> %s\n" k v)
                    mapping;
                  List.iter
                    (fun l -> layout_typectx layout_rty l |> print_endline)
                    ctxs;
                  failwith "you messed up")
              #: id.ty;
            ],
          new_ctx ))
      ([ unchanged_arg_name ], unchanged_context)
      (List.tl arg_names) (List.tl ctxs)

  let path_promotion (lc : LocalCtx.t) (id, rt, block_ctx) : t =
    let new_context, mapping = NameTracking.freshen block_ctx in
    let fresh_id = (Hashtbl.find mapping id.x) #: id.ty in
    let fresh_rt = Pieces.ut_subst rt mapping in
    NameTracking.add_ast fresh_id (NameTracking.get_ast id |> Option.get);

    ( fresh_id,
      fresh_rt,
      LocalCtx.promote_ctx_to_path new_context ~promote_ctx:lc )

  let existentialize ((name, ut, ctx) : t) : identifier * Nt.t rty =
    let local_ctx =
      Typectx.to_list ctx |> List.filter (fun { x; _ } -> x <> name.x)
    in
    let ext_rty = exists_rtys_to_rty local_ctx ut in
    (name, ext_rty)
end

module BlockSetF (B : Block_intf) : sig
  type t

  val empty : t
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
  (*   val extract : t -> B.t -> t * B.t option * Ptset.t * Ptset.t *)
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
      let uctx = !global_uctx |> Option.get in
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
  let is_empty (pm : t) : bool = P.is_empty pm
  let singleton (x : P.key) : t = P.singleton x ()
  let add_block (pm : t) x : t = P.add x () pm

  let find_block_opt (pm : t) (x : P.key) : P.key option =
    try Some (P.find x pm |> snd |> P.get_key) with Not_found -> None

  let get_idx (pm : t) (idx : Ptset.elt) : P.key = P.find_ix idx pm |> P.get_key
  let union (l : t) (r : t) : t = P.union l r
  let inter (l : t) (r : t) : t = P.inter l r
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

  let is_empty (map : t) : bool =
    List.for_all (fun (_, set) -> BlockSet.is_empty set) map

  let assert_valid (map : t) : unit =
    List.iter
      (fun (ty, set) ->
        let count = List.find_all (fun (t, _) -> t == ty) map in
        assert (List.length count == 1))
      map

  (** Add the (type, term pair to the map) *)
  let rec add (map : t) (term : B.t) (ty : Nt.t) : t =
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

  let init (inital_seeds : (B.t * Nt.t) list) : t =
    let aux (b_map : t) (term, ty) =
      (* layout_block term |> print_endline; *)
      add b_map term ty
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

  let check_coverage_with_args uctx block_id new_ut arg_names : bool =
    List.exists
      (fun ({ x; _ } as id : identifier) ->
        let arg_t = FrontendTyped.get_opt uctx x |> Option.get in
        let relation_result =
          Relations.typed_relation uctx x #: arg_t block_id.x #: new_ut.ty
        in
        Relations.Equiv == relation_result)
      arg_names

  let rec _add_to_path_specifc_list (path_specific : (LocalCtx.t * t) list)
      (local_ctx : LocalCtx.t) (b : B.t) ret_type =
    match path_specific with
    | [] -> [ (local_ctx, init [ (b, ret_type) ]) ]
    | (l, m) :: rest ->
        if l = local_ctx then (l, add m b ret_type) :: rest
        else (l, m) :: _add_to_path_specifc_list rest local_ctx b ret_type
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

  (* Promotable_paths should be empty if the new_blocks comes form a
       specific path *)
  (* Returns a block map for the new blocks... plus optionally a block map of
     those promoted to a new path *)
  (* Should we separate out the general and path specific cases? *)
  let increment (new_blocks : t) (old_blocks : t)
      ((component, (args, ret_type)) : Pieces.component * (Nt.t list * Nt.t))
      (promotable_paths : LocalCtx.t list) : t * (LocalCtx.t * t) list =
    let uctx = !global_uctx |> Option.get in

    (* Loop from 0 to args.len - 1 to choose an index for the `new_blocks` *)
    let res =
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
              let (arg_names : identifier list), (joined_ctx : LocalCtx.t) =
                Block.combine_all_args args
              in

              let block_id, term = Pieces.apply component arg_names in

              let new_uctx : uctx =
                LocalCtx.uctx_add_local_ctx uctx joined_ctx
              in

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
                           LocalCtx.promote_ctx_to_path joined_ctx
                             ~promote_ctx:x
                         in

                         let new_path_uctx =
                           LocalCtx.uctx_add_local_ctx uctx new_path_ctx
                         in

                         let new_path_ut =
                           Termcheck.term_type_infer_with_rec_check
                             new_path_uctx
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
    in
    assert_valid (fst res);
    List.iter (fun (l, m) -> assert_valid m) (snd res);
    res
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
        let { new_blocks; old_blocks } : t =
          add_map_with_cov_checked coll rest
        in
        let new_set = BlockMap.BlockSet.diff set (BlockMap.get old_blocks ty) in
        { new_blocks = BlockMap.add_list new_blocks new_set ty; old_blocks }
end

module SynthesisCollection = struct
  type t = {
    general_coll : BlockCollection.t;
    path_specific : (LocalCtx.t * BlockCollection.t) list;
  }
  (** A set of block_collections, a general one and some path specific ones *)

  let init (inital_seeds : BlockMap.t)
      (path_specific_seeds : (LocalCtx.t * BlockMap.t) list) : t =
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
      (path_specific : (LocalCtx.t * BlockCollection.t) list)
      (path_specific_maps : (LocalCtx.t * BlockMap.t) list) :
      (LocalCtx.t * BlockCollection.t) list =
    List.iter
      (fun (l, m) ->
        BlockMap.assert_valid m;
        assert (List.mem_assoc l path_specific))
      path_specific_maps;

    List.map
      (fun (l, bc) ->
        BlockCollection.assert_valid bc;
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

    print_endline "Increment General Collection";

    let new_collection =
      (* Iterate over all components *)
      List.fold_left
        (fun { general_coll; path_specific } op ->
          print_endline
            ("Incrementing with op: " ^ Pieces.layout_component (fst op));
          (* Iterate over sets of possible new maps *)
          let new_map, path_specific_maps =
            BlockMap.increment general_new_blocks general_old_blocks op
              promotable_paths
          in
          BlockCollection.assert_valid general_coll;
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
          print_endline "Increment Path Specific Collection";
          print_endline (layout_typectx layout_rty local_ctx);
          let path_specific_map =
            List.fold_left
              (fun acc op ->
                print_endline
                  ("Incrementing with op: " ^ Pieces.layout_component (fst op));
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
  let setup_type (x : (LocalCtx.t * BlockSetE.t * (Ptset.t * Ptset.t)) list)
      (target_ty : t rty) :
      (LocalCtx.t * BlockSetE.t * (identifier * t rty) * Ptset.t) list =
    let uctx = !global_uctx |> Option.get in

    (* print_endline (layout_rty target_ty); *)
    let res =
      List.map
        (fun (lc, map, (over_set, under_set)) ->
          match Ptset.min_elt_opt over_set with
          | Some i ->
              let id, rty = BlockSetE.get_idx map i in
              [ (lc, map, (id, rty), under_set) ]
          | None ->
              Ptset.fold
                (fun idx acc ->
                  let b = BlockSetE.get_idx map idx in
                  let p = BlockSetE.get_preds map b in
                  print_endline "Printing Preds";
                  BlockSetE.print_ptset map p;
                  (lc, map, b, p) :: acc)
                under_set [])
        (* get_max_elts under_set |> List.map (fun (b, s) -> (lc, map, b, s))) *)
        x
      |> List.concat
    in

    assert (sub_rty_bool uctx (unioned_rty_type2 res, target_ty));
    res

  (* Take blocks of different coverage types and join them together into full programs using non-deterministic choice *)
  let extract_blocks (collection : SynthesisCollection.t) (target_ty : t rty) :
      (LocalCtx.t * ExistentializedBlock.t) list =
    let target_nty = erase_rty target_ty in
    let uctx = !global_uctx |> Option.get in

    (* Create a target block that we are missing *)
    let target_block : ExistentializedBlock.t =
      ( (Rename.unique "missing") #: target_nty |> NameTracking.known_var,
        target_ty )
    in

    print_endline "Existentializing the general set";
    (* Get all blocks from the general collection *)
    let general_set =
      BlockCollection.get_full_map collection.general_coll |> fun x ->
      BlockMap.get x target_nty |> BlockSet.existentialize
    in

    (* The updated set is commented out because we don't to include the target
       block in later calculations *)
    let equal_block = BlockSetE.find_block_opt general_set target_block in

    assert (List.length collection.path_specific > 0);

    match equal_block with
    | Some b ->
        print_endline "Handling the equal_block case";
        let current : _ list =
          List.map
            (fun (lc, _) ->
              (* We already have our solution so we only need the set of paths *)
              ( lc,
                BlockSetE.empty,
                ExistentializedBlock.path_promotion lc b,
                Ptset.empty ))
            collection.path_specific
        in

        let current = minimize_num current target_ty in

        List.map (fun (lc, _, b, _) -> (lc, b)) current
    | _ -> (
        print_endline "Existentializing the path specific sets";
        Relations.clear_cache ();
        (* Get the sets for each path *)
        let path_specific_sets =
          List.map
            (fun (lc, bc) ->
              BlockCollection.get_full_map bc |> fun x ->
              BlockMap.get_opt x target_nty
              |> Option.value ~default:BlockSet.empty
              |> BlockSet.existentialize
              |> fun x -> (lc, x))
            collection.path_specific
        in

        (* We are going to do some normalization setup *)
        (* All General terms are going to get pushed into paths *)
        let path_specific_sets =
          List.map
            (fun ((lc : LocalCtx.t), bs) ->
              ( lc,
                BlockSetE.fold
                  (fun acc b ->
                    BlockSetE.add_block acc
                      (ExistentializedBlock.path_promotion lc b))
                  bs general_set ))
            path_specific_sets
        in

        Printf.printf "\n\n Path Specific collections we are interested in\n";
        List.iter
          (fun (ctx, set) ->
            let set = BlockSetE.add_block set target_block in
            Printf.printf "Path Specific Collection: %s\n"
              (layout_typectx layout_rty ctx);
            BlockSetE.print set;

            Printf.printf "\n\nPath Specific Succs\n\n";
            BlockSetE.print_ptset set (BlockSetE.get_succs set target_block);
            BlockSetE.print_ptset set (BlockSetE.get_preds set target_block))
          path_specific_sets;

        (* let block_options_in_each_path =
             List.map
               (fun (lc, bs) -> (lc, bs, BlockSetE.extract bs target_block))
               path_specific_sets
           in *)
        print_endline "ready to match";

        match
          List.find_map
            (fun (lc, path_set) ->
              BlockSetE.find_block_opt path_set target_block
              |> Option.map (fun b -> (lc, b)))
            path_specific_sets
        with
        | Some s ->
            print_endline "In the case where we have a match";
            (* print_endline (layout_typectx layout_rty lc);
               print_endline (Block.layout b);
               print_endline "We just shortcircuit in this case"; *)
            [ s ]
        | _ ->
            print_endline "In other case";

            (* Filter out those equal terms then to make my life cleaner *)
            let block_options_in_each_path =
              List.map
                (fun (lc, set) ->
                  let bs = BlockSetE.add_block set target_block in
                  let p = BlockSetE.get_preds bs target_block in
                  let s = BlockSetE.get_succs bs target_block in
                  BlockSetE.print_ptset bs p;
                  assert (not (Ptset.is_empty p && Ptset.is_empty s));
                  (lc, bs, (s, p)))
                path_specific_sets
            in

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
        (* If not, increment the collection and try again *)
        synthesis_helper (depth - 1) target_type
          (SynthesisCollection.increment collection operations)
          operations

  (** Given some initial setup, run the synthesis algorithm *)
  let synthesis (target_type : t rty) (max_depth : int)
      (inital_seeds : SynthesisCollection.t)
      (operations : (Pieces.component * (t list * t)) list) :
      (LocalCtx.t * _) list =
    (* SynthesisCollection.print inital_seeds; *)
    synthesis_helper max_depth target_type inital_seeds operations
end
