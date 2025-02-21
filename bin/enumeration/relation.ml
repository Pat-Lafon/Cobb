open Language.FrontendTyped
open Timeout
open Language
open Utils

(** The goal of this module is to provide utilites for the subtyping relation*)
module Relations : sig
  type relation = Equiv | ImpliesTarget | ImpliedByTarget | None | Timeout

  val layout : relation -> string
  val invert_relation : relation -> relation
  val is_equiv_or_timeout : relation -> bool
  val diff_base_type : t rty -> t rty -> bool

  (* TODO: comment this line out so everyone needs to use cache*)
  val is_sub_rty : uctx -> t rty -> t rty -> bool

  val is_sub_id_rty :
    uctx -> (t rty, string) typed -> (t rty, string) typed -> bool

  (* todo: comment this line out so everyone needs to use cache *)
  val typing_relation : uctx -> t rty -> t rty -> relation

  val typed_relation :
    uctx -> (t rty, string) typed -> (t rty, string) typed -> relation

  val check_coverage_with_args :
    uctx -> identifier -> t rty -> identifier list -> bool

  val check_cache : string -> string -> bool option
  val assert_string_not_in_cache : string -> unit
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
    type t = (string * string, bool) Hashtbl.t

    let cache : t = Hashtbl.create 10000
    let reset_cache () = Hashtbl.clear cache

    let add (l : string) (r : string) (is_sub : bool) : unit =
      Hashtbl.add cache (l, r) is_sub

    let check (l : string) (r : string) : bool option =
      Hashtbl.find_opt cache (l, r)
    (* match Hashtbl.find_opt cache (l, r) with
      | Some r -> Some r
      | None -> Hashtbl.find_opt cache (r, l) |> Option.map invert_relation *)
  end

  let is_equiv_or_timeout (r : relation) : bool =
    match r with Equiv | Timeout -> true | _ -> false

  let diff_base_type (l : t rty) (r : t rty) : bool =
    not (erase_rty l = erase_rty r)

  let check_cache = RelationCache.check

  let assert_string_not_in_cache (l : string) : unit =
    assert (
      Hashtbl.fold
        (fun (k1, k2) _ acc -> acc && not (k1 = l || k2 = l))
        RelationCache.cache true)

  let clear_cache () = RelationCache.reset_cache ()

  let is_sub_rty uctx l r =
    if diff_base_type l r then false
    else
      let res = Timeout.sub_rty_bool_or_timeout uctx (l, r) in
      match res with Result true -> true | _ -> false

  let is_sub_id_rty uctx (id : (t rty, string) typed) target_id =
    if id.x = target_id.x then true
    else if diff_base_type id.ty target_id.ty then false
    else
      match check_cache id.x target_id.x with
      | Some r -> r
      | None ->
          let res =
            let x =
              Timeout.sub_rty_bool_or_timeout uctx (id.ty, target_id.ty)
            in
            Timeout.timeout_eq (x, Timeout.Result true)
          in
          RelationCache.add id.x target_id.x res;
          res

  (* TODO: Where can this be replaced with cache access?*)
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

  let typed_relation ctx target_id id : relation =
    if diff_base_type target_id.ty id.ty then None
    else
      let implies_target = is_sub_id_rty ctx id target_id in
      let implied_by_target = is_sub_id_rty ctx target_id id in
      match (implies_target, implied_by_target) with
      | true, true -> Equiv
      | true, false -> ImpliesTarget
      | false, true -> ImpliedByTarget
      | false, false -> None

  let check_coverage_with_args uctx (block_id : identifier) new_ut arg_names :
      bool =
    List.exists
      (fun ({ x; _ } : identifier) ->
        let arg_t = FrontendTyped.get_opt uctx x |> Option.get in

        if not (is_sub_id_rty uctx x#:arg_t block_id.x#:new_ut) then false
        else is_sub_id_rty uctx block_id.x#:new_ut x#:arg_t
        (*  let relation_result =
          typed_relation uctx x #: arg_t block_id.x #: new_ut
        in
        (* TODO: Make this lazy/short-circuiting*)
        Equiv = relation_result *))
      arg_names
end
