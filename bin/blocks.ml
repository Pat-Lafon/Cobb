[@@@landmark "auto"]

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
open Pieces

(** Produces a list from 0..n-1*)
let range n = List.init n (fun x -> x)

(** https://stackoverflow.com/questions/40141955/computing-a-set-of-all-subsets-power-set
  *)
let rec superset_helper = function
  | [] -> [ [] ]
  | x :: xs ->
      let ps = superset_helper xs in
      ps @ List.map (fun ss -> x :: ss) ps

(* Superset, except remove the first element which is the nil element *)
let superset l = superset_helper l |> List.tl

(** Takes a list and performs a giant multi-cartesian product
  * Used to compute a new list of function arguments from a list of possible arguments for each position
*)
let rec n_cartesian_product = function
  | [] -> [ [] ]
  | x :: xs ->
      let rest = n_cartesian_product xs in
      List.concat (List.map (fun i -> List.map (fun rs -> i :: rs) rest) x)

(* let sample_ctx =
     [("x", UnderTy_base { basename = UT.default_v_name; normalty = NT.Ty_int; prop = (Lit (AVar { x = "x"; ty = NT.Ty_int })) })]
   let sample_subst = (Seq.return ("x", "y") |> Hashtbl.of_seq)

   let () = assert (ctx_subst sample_ctx sample_subst =
     [("y", UnderTy_base { basename = UT.default_v_name; normalty = NT.Ty_int; prop = (Lit (AVar { x = "y"; ty = NT.Ty_int })) })]) *)
(* let () = assert (ctx_subst [("x", UnderTy_base { basename = UT.default_v_name; normalty = NT.Ty_int; prop = Lit (ACint 1) })] (Seq.return ("x", "y") |> Hashtbl.of_seq) = [("y", UnderTy_base { basename = UT.default_v_name; normalty = NT.Ty_int; prop = Lit (ACint 1) })]) *)

let ctx_union_r (l : Typectx.ctx) (r : Typectx.ctx) =
  Pieces.map_fst (fun res -> l @ res) (Pieces.freshen r)

let%test "should fail" = 2 + 2 = 5
let%test "range" = range 5 = [ 0; 1; 2; 3; 4 ]

module Blocks = struct
  type base_type = Ntyped.t
  type block = id NNtyped.typed * UT.t * MustMayTypectx.ctx

  let block_compare ((id1, _, _) : block) ((id2, _, _) : block) =
    compare id1.x id2.x

  let block_list_compare (l1 : block list) (l2 : block list) =
    List.compare block_compare l1 l2

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

  let block_map_get (map : block_map) (ty : base_type) : block list =
    List.find_map
      (fun (ty', terms) -> if ty = ty' then Some terms else None)
      map
    |> Option.value ~default:[]

  let block_map_init (inital_seeds : (block * base_type) list) : block_map =
    let aux (b_map : block_map) (term, ty) = block_map_add b_map term ty in

    List.fold_left aux [] inital_seeds

  let base_type_to_string (ty : base_type) : id =
    Ntyped.sexp_of_t ty |> Core.Sexp.to_string_hum

  let u_type_to_string (ty : UT.t) : id =
    match ty with
    | UnderTy_base { basename; normalty; prop } ->
        Printf.sprintf "[%s: %s | %s]" basename (NT.to_string normalty)
          (P.to_string prop)
    | _ -> UT.sexp_of_t ty |> Core.Sexp.to_string_hum

  let block_to_string (({ x = name; ty }, ut, ctx) : block) : id =
    Printf.sprintf "%s: %s : %s\n" name
      (base_type_to_string (snd ty))
      (u_type_to_string ut)

  let block_map_print (map : block_map) : unit =
    let aux (ty, terms) =
      Printf.printf "Type: %s\n" (base_type_to_string ty);
      List.iter (fun t -> Printf.printf "\t%s\n" (block_to_string t)) terms
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

  (** For the block inference
    * Returns a mapping of all blocks, new and old *)
  let rec block_collection_get_full_map
      ({ new_blocks; old_blocks } : block_collection) : block_map =
    match new_blocks with
    | [] -> old_blocks
    | (ty, terms) :: rest ->
        let old_terms = block_map_get old_blocks ty in
        let new_terms = List.rev_append old_terms terms in
        (ty, new_terms)
        :: block_collection_get_full_map { new_blocks = rest; old_blocks }

  (** Given a collection, we want to construct a new set of blocks using some set of operations
    * Operations should not be valid seeds (i.e. must be operations that take arguments)*)
  let block_collection_increment (collection : block_collection)
      (operations : (Pieces.component * (base_type list * base_type)) list)
      (uctx : uctx) : block_collection =
    (* We pull aside our current `new_blocks`, these are the largest blocks in the collection *)
    let new_blocks = collection.new_blocks in
    (* New and old blocks get merged together *)
    (* These will make up the old blocks of the next collection *)
    let old_blocks = collection.old_blocks in

    (* For each operation in the list, we are going to iterate though it's argument types and pull out blocks that match said types *)
    (* Atleast one arguement use to create each new block must be from `new_blocks`, the rest are from `old_blocks`(which can also have blocks from `new_blocks`). This guarantees that all created blocks are of `new_blocks[i].size + 1` *)
    let resulting_blocks : (block * base_type) list =
      (* Loop over each of the operations*)
      List.concat_map
        (fun (component, (args, ret_type)) : (block * base_type) list ->
          (* Loop from 0 to args.len - 1 to choose an index for the `new_blocks`*)
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
                  let arg_names, joined_ctx =
                    List.fold_left2
                      (fun (args, acc_context) (id : id NNtyped.typed)
                           changed_ctx ->
                        let new_ctx, mapping =
                          ctx_union_r acc_context changed_ctx
                        in
                        ( args
                          @ [
                              ({ x = Hashtbl.find mapping id.x; ty = id.ty }
                                : id NNtyped.typed);
                            ],
                          new_ctx ))
                      ([ unchanged_arg_name ], unchanged_context)
                      (List.tl arg_names) (List.tl ctxs)
                  in

                  let (block_id : id NNtyped.typed), term =
                    Pieces.apply component arg_names
                  in

                  let new_uctx : uctx =
                    { ctx = joined_ctx; nctx = uctx.nctx; libctx = uctx.libctx }
                  in

                  let new_ut =
                    Typecheck.Undercheck.term_type_infer new_uctx
                      { x = term; ty = block_id.ty }
                  in

                  match new_ut with
                  | UnderTy_base { prop = Lit (ACbool false); _ } -> None
                  | _ ->
                      if
                        List.exists
                          (fun id ->
                            let arg_id, arg_t =
                              List.find (fun (id', _) -> id = id') joined_ctx
                            in

                            if not (NT.eq (MMT.erase arg_t) (UT.erase new_ut))
                            then false
                            else
                              Typecheck.Undersub.mmt_check_bool "" 0 joined_ctx
                                (MMT.Ut (MMT.UtNormal new_ut)) arg_t)
                          (arg_names
                          |> List.map (fun ({ x; ty } : id NNtyped.typed) -> x)
                          )
                      then
                        let () =
                          Printf.printf
                            "Failed to add the following block \n %s\n"
                            (Pieces.ast_to_string block_id.x)
                        in
                        None
                      else
                        let new_ctx =
                          Typectx.ut_force_add_to_right joined_ctx
                            (block_id.x, UtNormal new_ut)
                        in

                        Pieces.ast_to_string block_id.x
                        |> Printf.printf "Added the following block \n %s\n";
                        Some ((block_id, new_ut, new_ctx), ret_type))
                l)
            (range (List.length args) |> superset))
        operations
    in

    (* *)
    let new_map = block_map_init resulting_blocks in

    {
      new_blocks = new_map;
      old_blocks = block_collection_get_full_map collection;
    }
end

let under_ty_to_base_ty (ty : UT.t) : Blocks.base_type =
  match ty with
  | UnderTy_base { basename : id; normalty : normalty; prop : P.t } -> normalty
  | UnderTy_under_arrow _ -> failwith "not a base type"
  | UnderTy_over_arrow _ -> failwith "not a base type"
  | UnderTy_tuple _ -> failwith "not a base type"

module Synthesis = struct
  type program = NL.term NNtyped.typed

  (* Take blocks of different coverage types and join them together into full programs using non-deterministic choice *)
  let under_blocks_join (uctx : uctx) (collection : Blocks.block_collection)
      (target_ty : UT.t) : program option =
    (* Get all blocks from the collection*)
    let block_map = Blocks.block_collection_get_full_map collection in
    let base_type = under_ty_to_base_ty target_ty in
    let u_b_list = Blocks.block_map_get block_map base_type in

    (*
    print_endline "Blocks:";
    Blocks.block_collection_print collection; *)

    (* How do we want to combine blocks together? *)
    let super_type_list, sub_type_list =
      List.partition
        (fun (_, ut, ctx) ->
          (* Printf.printf "target_ty %s\n" (ut |> Blocks.u_type_to_string); *)
          Undersub.subtyping_check_bool "" 0 ctx ut target_ty)
        u_b_list
    in

    print_endline "Super Types:";
    List.iter
      (fun (id, _, _) ->
        Pieces.ast_to_string ~erased:true (id : id NNtyped.typed).x
        |> print_endline)
      super_type_list;
    print_endline "Sub Types:";
    List.iter
      (fun (id, _, _) ->
        Pieces.ast_to_string ~erased:true (id : id NNtyped.typed).x
        |> print_endline)
      sub_type_list;
    print_endline "End";

    (* I assume that there is always atleast one super type that satisfies the
       program because that type is of the generic generator *)
    let potential_program = List.hd super_type_list in
    (* We will check all of the other super_types to see if there is a program
       that is smaller but still works *)
    let potential_program =
      List.fold_left
        (fun p e ->
          let _, ut, ctx = p in
          let _, ut', ctx' = e in
          let combined_ctx, mapping = ctx_union_r ctx ctx' in
          let updated_ut = Pieces.ut_subst ut' mapping in

          if Undersub.subtyping_check_bool "" 0 combined_ctx ut updated_ut then
            p
          else e)
        potential_program (List.tl super_type_list)
    in

    (* actually do some joining of blocks*)
    if List.length sub_type_list > 1 then
      (* it is worth trying to *)
      failwith "todo"
    else (
      print_endline "Potential Program:";
      let id, _, _ = potential_program in
      Pieces.ast_to_string ~erased:true id.x |> print_endline;
      exit 1)

  let rec synthesis_helper (max_depth : int) (target_type : UT.t) (uctx : uctx)
      (collection : Blocks.block_collection)
      (operations :
        (Pieces.component * (Blocks.base_type list * Blocks.base_type)) list) :
      program option =
    match max_depth with
    | 0 ->
        (* Join blocks together into programs*)
        under_blocks_join uctx collection target_type
    | depth ->
        (* If not, increment the collection and try again*)
        synthesis_helper (depth - 1) target_type uctx
          (Blocks.block_collection_increment collection operations uctx)
          operations

  (** Given some initial setup, run the synthesis algorithm *)
  let synthesis (uctx : uctx) (target_type : UT.t) (max_depth : int)
      (inital_seeds : (Blocks.block * Blocks.base_type) list)
      (operations :
        (Pieces.component * (Blocks.base_type list * Blocks.base_type)) list) :
      program option =
    let init_collection = Blocks.block_collection_init inital_seeds in
    (*         Blocks.block_collection_print init_collection; *)
    synthesis_helper max_depth target_type uctx init_collection operations
end
