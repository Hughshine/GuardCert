(* Candidate selection is untrusted; each branch consumes an extracted
   certificate checker before the shared guarded whole-program host. *)
let propose instructions =
  try match Lazy.force GuardMemoryCandidate.template with
    | Some (GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "tile"; rows; columns]) ->
      Some (GuardMemoryUnifiedCompiler.GuardedTilingCandidate
        (GuardMemoryNumbers.import_integer (GuardMemoryCandidate.integer rows),
         GuardMemoryNumbers.import_integer (GuardMemoryCandidate.integer columns)))
    | _ -> match GuardMemoryCandidate.propose instructions with
      | Some (candidate,swaps) -> Some (GuardMemoryUnifiedCompiler.GuardedAffineCandidate (candidate,swaps))
      | None -> None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
