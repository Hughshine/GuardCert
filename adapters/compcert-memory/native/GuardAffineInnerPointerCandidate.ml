(* Untrusted metadata and candidate producers. The extracted source matcher,
   domain/dependence checker and machine lowerer validate every result. *)
let integer_setting name fallback =
  let value = match Sys.getenv_opt name with Some value -> value | None -> fallback in
  if String.length value > 128 then invalid_arg "affine-inner metadata integer limit";
  GuardMemoryNumbers.import_integer (Z.of_string value)

let profile source =
  try ClightAffineInnerPointerCandidates.propose_affine_inner_pointer_profile
    (integer_setting "GUARDCERT_AFFINE_ROW_CAP" "64")
    (integer_setting "GUARDCERT_AFFINE_COLUMN_CAP" "64")
    (integer_setting "GUARDCERT_AFFINE_GEOMETRY_CAP" "16")
    (integer_setting "GUARDCERT_AFFINE_EXTENT" "8192") source
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None

let step =
  let open GuardMemoryCandidate in function
  | List [Atom "swap"; position] -> GuardMemoryAffineReindex.MemoryReindexSwap (natural (small position))
  | List [Atom "shift"; position; delta] -> GuardMemoryAffineReindex.MemoryReindexShift
      (natural (small position), GuardMemoryNumbers.import_integer (integer delta))
  | List [Atom "skew"; target; source; factor] -> GuardMemoryAffineReindex.MemoryReindexSkew
      (natural (small target), natural (small source), GuardMemoryNumbers.import_integer (integer factor))
  | List [Atom "reflect"; position] -> GuardMemoryAffineReindex.MemoryReindexReflect (natural (small position))
  | _ -> invalid_arg "affine-inner index map"

let propose request =
  let open GuardMemoryCandidate in
  let open ClightAffineInnerPointerCandidates in
  try
    let instructions = request.affine_request_instructions in
    let caps = request.affine_request_geometry_caps in
    let scalar_count = List.length request.affine_request_context - List.length caps in
    if scalar_count < 0 then invalid_arg "affine-inner context";
    let zero = GuardMemoryNumbers.import_integer Z.zero in
    let one = GuardMemoryNumbers.import_integer Z.one in
    let lower = GuardMemoryNumbers.import_integer (Z.of_string "-2147483648") in
    let upper = GuardMemoryNumbers.import_integer (Z.of_string "2147483647") in
    let ranges = List.mapi (fun index cap -> (if index = 0 then one else zero), cap) caps
      @ List.init scalar_count (fun _ -> lower,upper) in
    let validator = List.map (fun (lo,hi) ->
      { GuardMemoryArrayBackend.MemoryNested.A.lower = lo; upper = hi }) ranges in
    let encoder = List.map (fun (lo,hi) ->
      { GuardMemoryPointerBackend.MemoryFramedNested.N.A.lower = lo; upper = hi }) ranges in
    let tiled row_width column_width raw_candidate wrong_witness =
      let row_width = GuardMemoryNumbers.import_integer (integer row_width) in
      let column_width = GuardMemoryNumbers.import_integer (integer column_width) in
      match propose_affine_inner_pointer_tiling request row_width column_width with
      | Some (loop,witnesses) ->
          let loop = match raw_candidate with Some syntax -> instantiate_at instructions None syntax | None -> loop in
          let witnesses = if wrong_witness then List.map (fun witness ->
            match witness.TilingWitness.stw_links with
            | first::rest -> { witness with TilingWitness.stw_links =
                { first with TilingWitness.tl_tile_size =
                    GuardMemoryNumbers.import_integer (Z.succ (GuardMemoryNumbers.export_integer first.TilingWitness.tl_tile_size)) }::rest }
            | [] -> witness) witnesses else witnesses in
          Some { affine_proposal_validator_bounds = validator; affine_proposal_encoder_bounds = encoder;
            affine_proposal_candidate = AffineInnerTilingProposal (loop,witnesses) }
      | None -> None in
    match Lazy.force template with
    | Some (List [Atom "tile"; row_width; column_width]) -> tiled row_width column_width None false
    | Some (List [Atom "tile-loop"; row_width; column_width; loop]) -> tiled row_width column_width (Some loop) false
    | Some (List [Atom "tile-wrong-witness"; row_width; column_width]) -> tiled row_width column_width None true
    | Some (List [Atom "schedule-explicit"; List schedules; List steps]) ->
        if List.length steps > 32 then invalid_arg "affine-inner map limit";
        let integer_rows schedule = List.map (function
          | List [List coefficients; constant] -> List.map (fun value -> GuardMemoryNumbers.import_integer (integer value)) coefficients,
              GuardMemoryNumbers.import_integer (integer constant)
          | _ -> invalid_arg "affine-inner schedule row") (members schedule) in
        Some { affine_proposal_validator_bounds = validator; affine_proposal_encoder_bounds = encoder;
          affine_proposal_candidate = AffineInnerScheduleProposal (List.map integer_rows schedules,List.map step steps) }
    | Some (List [Atom "map-index"; List steps; loop]) ->
        if List.length steps > 32 then invalid_arg "affine-inner map limit";
        Some { affine_proposal_validator_bounds = validator; affine_proposal_encoder_bounds = encoder;
          affine_proposal_candidate = AffineInnerMappedProposal (instantiate_at instructions None loop,List.map step steps) }
    | syntax -> match propose_template instructions syntax with
      | Some (loop,swaps) -> Some { affine_proposal_validator_bounds = validator; affine_proposal_encoder_bounds = encoder;
          affine_proposal_candidate = AffineInnerMappedProposal
            (loop,List.map (fun slot -> GuardMemoryAffineReindex.MemoryReindexSwap slot) swaps) }
      | None -> None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
