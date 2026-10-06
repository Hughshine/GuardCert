(* Untrusted proposals for the readonly API user. Both affine and tiling
   results are consumed by the extracted validators, never installed directly. *)
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

let propose instructions =
  let open GuardMemoryCandidate in
  let open ClightPolyhedralPreservation in
  try
    let syntax = Lazy.force template in
    match syntax with
    | Some (List [Atom "map-index"; List steps; loop]) ->
      if List.length steps > 32 then invalid_arg "affine index-map composition limit";
      Some (PreservingMappedCandidate
        (instantiate_at instructions None loop, List.map affine_step steps))
    | Some (List [Atom "tile"; rows; columns]) ->
      let rows, columns = integer rows, integer columns in
      let limit = Z.of_string "2147483647" in
      if Z.sign rows <= 0 || Z.sign columns <= 0 || Z.gt rows limit || Z.gt columns limit
      then None else Some (PreservingTilingCandidate
        (GuardMemoryNumbers.import_integer rows, GuardMemoryNumbers.import_integer columns))
    | _ -> match propose_template instructions syntax with
      | Some (loop, swaps) -> Some (PreservingMappedCandidate
          (loop, List.map (fun slot -> GuardMemoryAffineReindex.MemoryReindexSwap slot) swaps))
      | None -> None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
