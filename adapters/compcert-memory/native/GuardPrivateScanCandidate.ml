(* Only metadata and untrusted proposals cross this boundary. The extracted
   compiler generates and checks the actual pointer Loop before dispatch. *)
let affine_step =
  let open GuardMemoryCandidate in function
  | List [Atom "swap"; position] ->
    GuardMemoryAffineReindex.MemoryReindexSwap (natural (small position))
  | List [Atom "shift"; position; delta] ->
    GuardMemoryAffineReindex.MemoryReindexShift
      (natural (small position), GuardMemoryNumbers.import_integer (integer delta))
  | List [Atom "skew"; target; source; factor] ->
    GuardMemoryAffineReindex.MemoryReindexSkew
      (natural (small target), natural (small source), GuardMemoryNumbers.import_integer (integer factor))
  | List [Atom "reflect"; position] ->
    GuardMemoryAffineReindex.MemoryReindexReflect (natural (small position))
  | _ -> invalid_arg "affine index-map step"

let propose request =
  let open GuardMemoryCandidate in
  let open ClightParamPointerCandidates in
  let instructions = request.pointer_request_instructions in
  let dimensions = GuardMemoryScheduleInput.natural_size request.pointer_request_coordinates in
  let arity = GuardMemoryScheduleInput.natural_size request.pointer_request_context_arity in
  try
    match Lazy.force template with
    | Some (List [Atom "schedule"; List axes; List steps]) ->
      if List.length steps > 32 then invalid_arg "schedule index-map limit";
      Some (PointerScheduleProposal
        (GuardMemoryScheduleInput.instantiate dimensions arity instructions axes,
         List.map affine_step steps))
    | Some (List [Atom ("schedule-explicit" | "schedule-list"); List schedules; List steps]) ->
      if List.length steps > 32 then invalid_arg "schedule index-map limit";
      Some (PointerScheduleProposal (GuardMemoryScheduleInput.explicit schedules,
        List.map affine_step steps))
    | Some (List [Atom "map-index"; List steps; loop]) ->
      if List.length steps > 32 then invalid_arg "affine index-map composition limit";
      Some (PointerMappedProposal (instantiate_at instructions None loop, List.map affine_step steps))
    | Some (List [Atom "tile"; rows; columns]) ->
      let rows, columns = integer rows, integer columns in
      let limit = Z.of_string "2147483647" in
      if Z.sign rows <= 0 || Z.sign columns <= 0 || Z.gt rows limit || Z.gt columns limit
      then None else Some (PointerTilingProposal
        (GuardMemoryNumbers.import_integer rows, GuardMemoryNumbers.import_integer columns))
    | syntax -> match propose_template instructions syntax with
      | Some (loop,swaps) -> Some (PointerMappedProposal
          (loop,List.map (fun slot -> GuardMemoryAffineReindex.MemoryReindexSwap slot) swaps))
      | None -> None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
