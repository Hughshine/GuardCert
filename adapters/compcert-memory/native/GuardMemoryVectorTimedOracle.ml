(* Observe vector search data through the unchanged extracted LCF checks.
   The underlying oracle retains its original limits and fault-test option. *)
open CstrLCF
let add = GuardMemoryVectorOracle.add
let is_empty input =
  if not (GuardMemoryPhaseTrace.enabled ()) then GuardMemoryVectorOracle.is_empty input else
  let query = !GuardMemoryVectorOracle.searches + 1 in
  let wall = Unix.gettimeofday () in
  let cpu = GuardMemoryPhaseTrace.cpu_seconds () in
  Printf.eprintf "GUARDCERT_ORACLE query=%d event=begin constraints=%d phase=%S\n%!"
    query (List.length input.cert) !GuardMemoryPhaseTrace.current_stage;
  let result = GuardMemoryVectorOracle.is_empty input in
  Printf.eprintf "GUARDCERT_ORACLE query=%d event=end contradiction=%b wall_seconds=%.6f cpu_seconds=%.6f exhausted=%d\n%!"
    query (Option.is_some result) (Unix.gettimeofday () -. wall)
    (GuardMemoryPhaseTrace.cpu_seconds () -. cpu) !GuardMemoryVectorOracle.exhausted;
  result
