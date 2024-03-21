open Typing
open Term
open Mtyped
open Nt
open Rty
open Typing.Termcheck
open Language.FrontendTyped
open Utils
open Cty
open Pieces
open Frontend_opt.To_typectx
open Zzdatatype.Datatype
open Timeout
open Tracking

module rec Relations : sig
  type relation = Equiv | ImpliesTarget | ImpliedByTarget | None | Timeout

  val sexp_of_relation : relation -> Core.Sexp.t
  val is_equiv_or_timeout : relation -> bool
  val rty_typing_relation : uctx -> t rty -> t rty -> relation
  val block_typing_relation : uctx -> Blocks.block -> Blocks.block -> relation
end = struct
  type relation = Equiv | ImpliesTarget | ImpliedByTarget | None | Timeout
  [@@deriving sexp]

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

  let block_typing_relation (uctx : uctx) (target_block : Blocks.block)
      (block : Blocks.block) =
    let _, target_ty, target_ctx = target_block in
    let _, ty, ctx = block in
    if diff_base_type target_ty ty then None
    else
      let combined_ctx, mapping = Blocks.local_ctx_union_r target_ctx ctx in
      let updated_ty = Pieces.ut_subst ty mapping in

      rty_typing_relation
        (Blocks.uctx_add_local_ctx uctx combined_ctx)
        target_ty updated_ty
end

and Blocks : sig
  type base_type = t
  type local_ctx = base_type rty Typectx.ctx
  type block = identifier * t rty * local_ctx
  type block_map = (base_type * block list) list
  type block_collection = { new_blocks : block_map; old_blocks : block_map }

  (* Combining to local contexts together for renaming *)
  val local_ctx_union_r :
    local_ctx -> local_ctx -> local_ctx * (string, string) Hashtbl.t

  val uctx_add_local_ctx : uctx -> local_ctx -> uctx

  (* String/printing facilites *)
  val layout_block : block -> string
  val block_collection_print : block_collection -> unit

  (* *)
  val block_map_get : block_map -> base_type -> block list

  (* Block Collection facilities *)
  val block_collection_init : (block * base_type) list -> block_collection
  val block_collection_get_full_map : block_collection -> block_map

  val block_collection_increment :
    block_collection ->
    (Pieces.component * (base_type list * base_type)) list ->
    uctx ->
    block_collection
end = struct
  type base_type = t
  type local_ctx = base_type rty Typectx.ctx
  type block = identifier * t rty * local_ctx

  let local_ctx_union_r (Typectx l : local_ctx) (r : local_ctx) :
      local_ctx * (string, string) Hashtbl.t =
    map_fst
      (fun (Typectx.Typectx res) -> Typectx.Typectx (l @ res))
      (NameTracking.freshen r)

  let uctx_add_local_ctx (uctx : uctx) (ctx : local_ctx) : uctx =
    {
      uctx with
      local_ctx =
        (* Typectx.add_to_rights *)
        Typectx
          (* (List.fold_left
             (fun acc x ->
               if List.exists (fun y -> x == y) acc then acc else x :: acc)
             (Typectx.to_list uctx.local_ctx)
             (Typectx.to_list ctx)) *)
          (List.concat [ Typectx.to_list ctx; Typectx.to_list uctx.local_ctx ]);
    }

  (* For a given type, check if any of the elements satisfy the function f *)

  (* bool -> var1, true
     int -> 0, 1, ... *)
  type block_map = (base_type * block list) list

  (* Blocks are added to the `new_blocks` field *)
  (* `new_blocks` get shifted over to `old_blocks` when we increment to a new, larger set of blocks *)
  type block_collection = { new_blocks : block_map; old_blocks : block_map }

  let base_type_to_string (ty : base_type) : string = layout_ty ty

  let layout_block ((name, ut, ctx) : block) : string =
    Printf.sprintf "%s⊢ %s: %s : %s\n"
      (layout_typectx layout_rty ctx ^ " ")
      (Pieces.ast_to_string name)
      (base_type_to_string name.ty)
      (layout_rty ut)

  (** Enforces uniqueness of the inner block list *)
  let rec block_list_add (lst : block list) (term : block) : block list =
    match lst with
    | [] -> [ term ]
    | hd :: tl ->
        if hd = term then failwith "term is not unique in block list"
        else hd :: block_list_add tl term

  let block_list_add_list (lst : block list) (term_list : block list) :
      block list =
    List.fold_left (fun acc x -> block_list_add acc x) term_list lst

  (** Checks if any element of the block list satisfies the function f
    * Like when checking that there is an equivalent block *)
  let block_list_any (lst : block list) (f : block -> bool) : bool =
    List.find_opt f lst |> Option.is_some

  let block_list_print (lst : block list) : unit =
    List.iter (fun t -> Printf.printf "\t%s\n" (layout_block t)) lst

  (** Add the (type, term pair to the map) *)
  let rec block_map_add (map : block_map) (term : block) (ty : base_type) :
      block_map =
    match map with
    | [] -> [ (ty, [ term ]) ]
    | (ty', terms) :: rest ->
        if eq ty ty' then (ty, block_list_add terms term) :: rest
        else (ty', terms) :: block_map_add rest term ty

  (** Add the (type, term pair to the map) *)
  let rec block_map_add_list (map : block_map) (term_list : block list)
      (ty : base_type) : block_map =
    match map with
    | [] -> [ (ty, term_list) ]
    | (ty', terms) :: rest ->
        if eq ty ty' then (ty, block_list_add_list terms term_list) :: rest
        else (ty', terms) :: block_map_add_list rest term_list ty

  let block_map_get (map : block_map) (ty : base_type) : block list =
    List.assoc_opt ty map |> Option.value ~default:[]

(*   let block_map_remove (map : block_map) (ty : base_type) : block_map =
    List.remove_assoc ty map *)

  (* For a given type, check if any of the elements satisfy the function f *)
  let block_map_any (map : block_map) (ty : base_type) (f : block -> bool) :
      bool =
    block_list_any (block_map_get map ty) f

  let block_map_init (inital_seeds : (block * base_type) list) : block_map =
    let aux (b_map : block_map) (term, ty) = block_map_add b_map term ty in
    List.fold_left aux [] inital_seeds

  let block_map_print (map : block_map) : unit =
    let aux (ty, terms) =
      Printf.printf "Type: %s\n" (base_type_to_string ty);
      block_list_print terms
    in
    List.iter aux map

  (** Initialize a block collection with the given seeds values
    * Seeds are initial blocks that are just variables, constants, or operations that take no arguments (or just unit) *)
  let block_collection_init (inital_seeds : (block * base_type) list) :
      block_collection =
    let new_blocks : block_map = block_map_init inital_seeds in
    { new_blocks; old_blocks = [] }

  let block_collection_print ({ new_blocks; old_blocks } : block_collection) :
      unit =
    Printf.printf "New Blocks:\n";
    block_map_print new_blocks;
    Printf.printf "Old Blocks:\n";
    block_map_print old_blocks

  (* For a given type, check if any of the elements satisfy the function f *)
  let block_collection_any ({ new_blocks; old_blocks } : block_collection)
      (ty : base_type) (f : block -> bool) : bool =
    block_map_any new_blocks ty f || block_map_any old_blocks ty f

  let block_collection_add ({ new_blocks; old_blocks } : block_collection)
      (term : block) (ty : base_type) : block_collection =
    let new_blocks = block_map_add new_blocks term ty in
    { new_blocks; old_blocks }

  let block_collection_coverage_equiv_add (uctx : uctx)
      (coll : block_collection) (term : block) (ty : base_type) :
      block_collection =
    if
      block_collection_any coll ty (fun target_block ->
          Relations.block_typing_relation uctx term target_block
          |> Relations.is_equiv_or_timeout)
    then coll
    else block_collection_add coll term ty

  (** For the block inference
    * Returns a mapping of all blocks, new and old *)
  let rec block_collection_get_full_map
      ({ new_blocks; old_blocks } : block_collection) : block_map =
    match new_blocks with
    | [] -> old_blocks
    | (ty, terms) :: rest ->
        let rest =
          block_collection_get_full_map { new_blocks = rest; old_blocks }
        in
        block_map_add_list rest terms ty

        (* (*  block_map_add rest (ty, terms) ty *)
        let old_terms = block_map_get old_blocks ty in
        let remaining_old_blocks = block_map_remove old_blocks ty in
        let new_terms = List.rev_append old_terms terms in
        (ty, new_terms)
        :: block_collection_get_full_map
             { new_blocks = rest; old_blocks = remaining_old_blocks } *)

  (** Given a collection, we want to construct a new set of blocks using some set of operations
    * Operations should not be valid seeds (i.e. must be operations that take
      arguments) *)
  let block_collection_increment (collection : block_collection)
      (operations : (Pieces.component * (base_type list * base_type)) list)
      (uctx : uctx) : block_collection =
    print_endline "Doing increment";
    (* We pull aside our current `new_blocks`, these are the largest blocks in the collection *)
    let new_blocks = collection.new_blocks in
    (* New and old blocks get merged together *)
    (* These will make up the old blocks of the next collection *)
    let old_blocks = collection.old_blocks in

    (* For each operation in the list, we are going to iterate though it's argument types and pull out blocks that match said types *)
    (* Atleast one arguement use to create each new block must be from `new_blocks`, the rest are from `old_blocks`(which can also have blocks from `new_blocks`). This guarantees that all created blocks are of `new_blocks[i].size + 1` *)
    let resulting_blocks : (block * base_type) list =
      (* Loop over each of the operations *)
      List.concat_map
        (fun (component, (args, ret_type)) : (block * base_type) list ->
          (* Loop from 0 to args.len - 1 to choose an index for the `new_blocks`
          *)
          List.concat_map
            (fun new_set ->
              (* Loop over each of the arguments, getting a list of blocks for each one *)
              let l =
                List.mapi
                  (fun j ty : block list ->
                    if List.mem j new_set then block_map_get new_blocks ty
                    else block_map_get old_blocks ty)
                  args
              in
              let l = n_cartesian_product l in

              List.filter_map
                (fun (args : block list) : (block * base_type) option ->
                  let arg_names = List.map (fun (id, _, _) -> id) args in
                  let ctxs = List.map (fun (_, _, ctx) -> ctx) args in

                  let unchanged_arg_name = List.hd arg_names in
                  let unchanged_context = List.hd ctxs in

                  (* Correct joining of contexts? *)
                  let (arg_names : identifier list), (joined_ctx : local_ctx) =
                    List.fold_left2
                      (fun ((args : identifier list), (acc_context : local_ctx))
                           (id : identifier) changed_ctx :
                           (identifier list * local_ctx) ->
                        let new_ctx, mapping =
                          local_ctx_union_r acc_context changed_ctx
                        in
                        ( args @ [ (Hashtbl.find mapping id.x) #: id.ty ],
                          new_ctx ))
                      ([ unchanged_arg_name ], unchanged_context)
                      (List.tl arg_names) (List.tl ctxs)
                  in

                  let block_id, term = Pieces.apply component arg_names in

                  let new_uctx : uctx = uctx_add_local_ctx uctx joined_ctx in

                  let new_ut =
                    Termcheck.term_type_infer new_uctx
                      { x = term.x; ty = block_id.ty }
                    |> Option.get
                  in

                  match new_ut.ty with
                  | RtyBase
                      { cty = Cty { phi = Lit { x = AC (B false); _ }; _ }; _ }
                    ->
                      (* The block does not type check most likely because one of
                         the arguments does not meet the precondition for the
                         component *)
                      None
                  | _ ->
                      if
                        List.exists
                          (fun (id : string) ->
                            let joined_uctx =
                              uctx_add_local_ctx uctx joined_ctx
                            in
                            let arg_t = get_opt joined_uctx id |> Option.get in
                            let relation_result =
                              Relations.rty_typing_relation joined_uctx arg_t
                                new_ut.ty
                            in
                            Relations.is_equiv_or_timeout relation_result)
                          (arg_names
                          |> List.map (fun ({ x; _ } : identifier) -> x))
                      then
                        (* let () =
                             Printf.printf
                               "Failed to add the following block \n %s\n"
                               (Pieces.ast_to_string block_id.x)
                           in *)
                        None
                      else
                        let new_ctx =
                          Typectx.add_to_right joined_ctx
                            { x = block_id.x; ty = new_ut.ty }
                        in

                        (*
                        Printf.printf "Added the following block \n %s\n %s\n"
                          (Pieces.ast_to_string block_id.x)
                          (u_type_to_string new_ut);
                        *)
                        Some ((block_id, new_ut.ty, new_ctx), ret_type))
                l)
            (range (List.length args) |> superset))
        operations
    in

    let new_map = block_map_init resulting_blocks in

    let new_collection =
      { new_blocks = []; old_blocks = block_collection_get_full_map collection }
    in

    print_endline "Checking coverage Equivalence";
    List.fold_left
      (fun (coll : block_collection) (base_type, block_list) ->
        List.fold_left
          (fun coll block ->
            layout_block block |> print_endline;
            block_collection_coverage_equiv_add uctx coll block base_type)
          coll block_list)
      new_collection new_map
end

module Synthesis = struct
  type program = (t, t term) Mtyped.typed

  (* Take blocks of different coverage types and join them together into full programs using non-deterministic choice *)
  let under_blocks_join (uctx : uctx) (collection : Blocks.block_collection)
      (target_ty : t rty) : program option =
    (* Get all blocks from the collection*)
    let block_map = Blocks.block_collection_get_full_map collection in
    let base_type = erase_rty target_ty in
    let u_b_list = Blocks.block_map_get block_map base_type in

    (* todo remove dubs from typeing contexts now that not all values are
       freshened *)
    (* How do we want to combine blocks together? *)
    let groups =
      group_by
        (fun (id, ut, ctx) ->
          Blocks.layout_block (id, ut, ctx) |> print_endline;
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
    in

    print_endline "\n\n";
    let _ =
      List.iter
        (fun ((g, es) : Relations.relation * Blocks.block list) ->
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
    in
    let super_type_list =
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
    in

    let potential_program =
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
    in

    (* actually do some joining of blocks *)
    if List.length sub_type_list > 1 then
      (* it is worth trying to *)
      failwith "todo"
    else (
      print_endline "Potential Program:";
      (match potential_program with
      | Some (id, _, _) ->
          Pieces.ast_to_string ~erased:true id |> print_endline;
          ()
      | None -> ());
      failwith "todo")

  let rec synthesis_helper (max_depth : int) (target_type : t rty) (uctx : uctx)
      (collection : Blocks.block_collection)
      (operations :
        (Pieces.component * (Blocks.base_type list * Blocks.base_type)) list) :
      program option =
    match max_depth with
    | 0 ->
        Blocks.block_collection_print collection;
        (* Join blocks together into programs *)
        under_blocks_join uctx collection target_type
    | depth ->
        (* If not, increment the collection and try again *)
        synthesis_helper (depth - 1) target_type uctx
          (Blocks.block_collection_increment collection operations uctx)
          operations

  (** Given some initial setup, run the synthesis algorithm *)
  let synthesis (uctx : uctx) (target_type : t rty) (max_depth : int)
      (inital_seeds : (Blocks.block * Blocks.base_type) list)
      (operations :
        (Pieces.component * (Blocks.base_type list * Blocks.base_type)) list) :
      program option =
    let init_collection = Blocks.block_collection_init inital_seeds in
    Blocks.block_collection_print init_collection;
    synthesis_helper max_depth target_type uctx init_collection operations
end
