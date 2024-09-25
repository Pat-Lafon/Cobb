open Language.FrontendTyped
open Utils
open Pieces
open Zzdatatype.Datatype
open Language
open Context
open Block
open Extraction
open Synthesiscollection

module Synthesis = struct
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
end
