(* Finite untrusted representation search for the reindexed tiling checker. *)
include GuardSelectedDoubleAffineTiledCandidate
let choices () = if not (enabled ()) then GuardSelectedDoubleWitnessPolicy.choices () else
  let axes = match Sys.getenv_opt "GUARDCERT_DOUBLE_WITNESS_AXES" with
    | None -> 6 | Some text -> int_of_string text in
  if axes < 0 || axes > 32 then invalid_arg "witness axes must be in [0,32]";
  [] :: List.init (max 0 (axes-1)) (fun axis -> [nat axis])
