open Block
open Pomap
open Relation

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
  val layout : t -> string
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

  let layout (pm : t) : string =
    let res = Buffer.create 256 in
    D.fprintf (Format.formatter_of_buffer res) pm;
    Buffer.contents res

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
