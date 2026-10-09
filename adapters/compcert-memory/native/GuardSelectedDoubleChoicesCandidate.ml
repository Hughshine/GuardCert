(* Per-site witness choices are untrusted; each retry goes through the extracted
   factory. Memoization shares an identical external scheduling proposal. *)
let choices () = match GuardSelectedDoubleCandidate.mode () with
  | "affine" -> [[]; [GuardSelectedDoubleCandidate.nat 0]]
  | "wrong-witness" -> [[]]
  | _ -> [[]]
let proposals = ref []
let schedule before = match List.find_opt (fun (source,_) -> source = before) !proposals with
  | Some (_,after) ->
    Printf.eprintf "GUARDCERT_DOUBLE_PROPOSAL_REUSED\n%!"; after
  | None ->
    let after = GuardSelectedDoubleCandidate.schedule before in
    proposals := (before,after) :: !proposals; after
let private_count = GuardSelectedDoubleCandidate.private_count
let trace_clight = GuardSelectedReductionCandidate.trace_clight
