open Block
open Core

type priority_list = (int, Block.t list) Hashtbl.t

module BBQueue = struct
  type t = PreBlock.t Pairing_heap.t

  let init () : t =
    Pairing_heap.create ?min_size:(Some 256)
      ~cmp:(fun (a : PreBlock.t) b -> Int.compare a.cost b.cost)
      ()

  let add (queue : t) (block : PreBlock.t) : unit = Pairing_heap.add queue block
  let next (queue : t) : PreBlock.t option = Pairing_heap.pop queue
end

let ( -- ) i j =
  let rec aux n acc = if n < i then acc else aux (n - 1) (n :: acc) in
  aux j []

(* let _gen_helper (lst : int list) : int list list =
     List.map
       (0 -- (List.length lst - 1))
       ~f:(fun i -> List.mapi lst ~f:(fun j el -> if i = j then el + 1 else el))

   let rec _gen_priority_list_helper (target_cost : int) (sum : int) (lst : _) :
       int list list =
     if target_cost > sum then
       List.map (_gen_helper lst) ~f:(fun x ->
           _gen_priority_list_helper target_cost (sum + 1) x)
       |> List.concat
     else [ lst ]
*)
let _more_efficient_gen_priority_list_helper (target_cost : int) (arity : int) :
    int list list =
  assert (target_cost >= arity);

  let l =
    List.fold
      (0 -- (arity - 1) |> List.rev)
      ~init:[ (0, []) ]
      ~f:(fun acc (remaining_args : int) ->
        List.map
          (acc : (int * int list) list)
          ~f:(fun (current_cost, lst) ->
            if remaining_args = 0 then
              [ (current_cost, (target_cost - current_cost) :: lst) ]
            else
              List.map
                (1 -- (target_cost - remaining_args - current_cost))
                ~f:(fun i : (int * int list) -> (current_cost + i, i :: lst)))
        |> List.concat)
  in
  List.map l ~f:(fun (_, lst) -> lst)

(** Given a priority and an arity, find all valid smaller combinations
 * Zero is not allowed, must be of length arity, must be smaller than priority
 * Hacks are allowed *)
let _gen_priority_list (target_cost : int) (arity : int) : int list list =
  if target_cost < arity then (
    print_endline "Warning: target_cost < arity";
    [])
  else _more_efficient_gen_priority_list_helper target_cost arity

(* let x = List.init arity ~f:(fun _ -> 1) in
   let res = _gen_priority_list_helper target_cost arity x in
   List.dedup_and_sort res ~compare:[%compare: int list]
*)
module PriorityBBMap = struct
  type t = (int, (Nt.t, Block.t list) Hashtbl.t) Hashtbl.t

  let assert_valid (t : t) : unit =
    assert (Hashtbl.keys t |> List.for_all ~f:(fun x -> x >= 0));
    assert (
      Hashtbl.for_all t ~f:(fun data ->
          Hashtbl.for_all data ~f:(fun data -> not (List.is_empty data))))

  let empty () : t = Hashtbl.create (module Int)

  let add (t : t) (block : Block.t) : unit =
    let cost = block.cost in
    Hashtbl.update t cost ~f:(function
      | Some blocks ->
          Hashtbl.update blocks (Block.to_nty block) ~f:(fun blst ->
              match blst with None -> [ block ] | Some lst -> block :: lst);
          blocks
      | None ->
          Hashtbl.of_alist_exn (module Nt) [ (Block.to_nty block, [ block ]) ])

  let init (seeds : Block.t list) : t =
    let t = empty () in
    List.iter seeds ~f:(fun block -> add t block);
    t

  let get (t : t) (cost : int) : (Nt.t, Block.t list) Hashtbl.t option =
    Hashtbl.find t cost

  let get_args (t : t) (target_cost : int) (args : Nt.t list) :
      Block.t list list =
    let variations_of_cost =
      _gen_priority_list target_cost (List.length args)
    in
    List.concat_map variations_of_cost ~f:(fun new_set ->
        List.mapi args ~f:(fun j ty ->
            match get t (List.nth_exn new_set j) with
            | Some blocks -> Hashtbl.find blocks ty |> Option.value ~default:[]
            | None -> [])
        |> Utils.n_cartesian_product)

  let layout (t : t) : string =
    let res = Buffer.create 256 in
    Hashtbl.iteri t ~f:(fun ~key ~data ->
        Buffer.add_string res (Printf.sprintf "Cost: %d\n" key);
        Hashtbl.iteri data ~f:(fun ~key ~data ->
            Buffer.add_string res (Printf.sprintf "Type: %s\n" (Nt.layout key));
            List.iter data ~f:(fun block ->
                Buffer.add_string res (Block.layout block);
                Buffer.add_char res '\n')));

    Buffer.contents res

  let print (t : t) : unit = print_endline (layout t)
end
(*
let%test_unit "gen_priority_list" =
  let res = _gen_priority_list 3 2 in
  let expected = [ [ 1; 2 ]; [ 2; 1 ] ] in
  [%test_eq: int list list] res expected

let%test_unit "gen_priority_list2" =
  let res = _gen_priority_list 4 2 in
  let expected = [ [ 1; 3 ]; [ 2; 2 ]; [ 3; 1 ] ] in
  [%test_eq: int list list] res expected

let%test_unit "gen_priority_list3" =
  let res = _gen_priority_list 5 3 in
  let expected =
    [
      [ 1; 1; 3 ];
      [ 1; 2; 2 ];
      [ 1; 3; 1 ];
      [ 2; 1; 2 ];
      [ 2; 2; 1 ];
      [ 3; 1; 1 ];
    ]
  in
  [%test_eq: int list list] res expected *)

let%test_unit "gen_priority_list_big" =
  let res = _more_efficient_gen_priority_list_helper 3 2 in
  let expected = [ [ 2; 1 ]; [ 1; 2 ] ] in
  [%test_eq: int list list] res expected

let%test_unit "gen_priority_list_big" =
  let res = _more_efficient_gen_priority_list_helper 4 2 in
  let expected = [ [ 3; 1 ]; [ 2; 2 ]; [ 1; 3 ] ] in
  [%test_eq: int list list] res expected

let%test_unit "gen_priority_list_big" =
  let res = _more_efficient_gen_priority_list_helper 5 3 in
  let expected =
    [
      [ 3; 1; 1 ];
      [ 2; 2; 1 ];
      [ 1; 3; 1 ];
      [ 2; 1; 2 ];
      [ 1; 2; 2 ];
      [ 1; 1; 3 ];
    ]
  in
  [%test_eq: int list list] res expected

(* let%test_unit "gen_priority_list_big" =
   let res = _more_efficient_gen_priority_list_helper 21 4 in
   let expected = [] in
   [%test_eq: int list list] res expected *)
