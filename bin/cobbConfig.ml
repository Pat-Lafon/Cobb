type t = {
  synth_bound : int;
  synth_rlimit : int option; [@default None]
  type_rlimit : int option; [@default None]
  comp_path : string; [@default "components.txt"]
  imprecise : bool; [@default false]
}
[@@deriving of_yojson { strict = true }]

include ConfigSection.Make (struct
  type nonrec t = t

  let name = "cobb"
  let of_yojson = of_yojson
end)

let bootstrap root =
  Abduction.AbductionConfig.bootstrap root;
  set (of_meta_config root)
