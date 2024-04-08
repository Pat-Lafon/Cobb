open Rty
open Language.FrontendTyped

module Timeout = struct
  type bool_or_timeout = Result of bool | Timeout

  let timeout_eq = function
    | Timeout, Timeout -> true
    | Result x, Result y -> x = y
    | _ -> false

  let bool_or_timeout_to_string = function
    | Result b -> string_of_bool b
    | Timeout -> "timeout"

  let sub_rty_bool_or_timeout (ctx : uctx) (l : t rty * t rty) : bool_or_timeout
      =
    let r = Typing.Termcheck.sub_rty_bool ctx l in
    Result r
  (* Commented out because everything that is false timesout at the moment *)
  (* if !Backend.Check.smt_timeout_flag then Timeout else Result r *)
end
