open Language

module Timeout = struct
  type bool_or_timeout = Result of bool | Timeout

  let timeout_eq = function
    | Timeout, Timeout -> true
    | Result x, Result y -> x = y
    | _ -> false

  let bool_or_timeout_to_string = function
    | Result b -> string_of_bool b
    | Timeout -> "timeout"

  let sub_rty_bool_or_timeout ctx (l : Nt.t rty * Nt.t rty) : bool_or_timeout =
    let r = Auxtyping.sub_rty ctx l in
    Result r
end
