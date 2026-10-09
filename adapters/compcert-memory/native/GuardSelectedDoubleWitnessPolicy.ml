(* Untrusted bounded witness search for the existing proved choices compiler.
   Each attempted witness still passes the extracted source/candidate factory.
   These choices cover identity and one adjacent interchange; they do not cover
   arbitrary affine changes, compound permutations, fission or tiling. *)
let choices () = match GuardSelectedDoubleCandidate.mode () with
  | "affine" ->
    let axes = match Sys.getenv_opt "GUARDCERT_DOUBLE_WITNESS_AXES" with
      | None -> 6 | Some text -> int_of_string text in
    if axes < 0 || axes > 32 then invalid_arg "witness axes must be in [0,32]";
    [] :: List.init (max 0 (axes - 1))
      (fun index -> [GuardSelectedDoubleCandidate.nat index])
  | _ -> [[]]
let schedule = GuardSelectedDoubleChoicesCandidate.schedule
let private_count = GuardSelectedDoubleChoicesCandidate.private_count
let trace_clight = GuardSelectedDoubleChoicesCandidate.trace_clight
