(* Candidate selection is untrusted; each branch consumes an extracted
   certificate checker before the shared guarded whole-program host. *)
module L = GuardMemoryLoops.L

let affine_step =
  let open GuardMemoryCandidate in function
  | List [Atom "swap"; position] ->
    GuardMemoryAffineReindex.MemoryReindexSwap (natural (small position))
  | List [Atom "shift"; position; delta] ->
    GuardMemoryAffineReindex.MemoryReindexShift
      (natural (small position),GuardMemoryNumbers.import_integer (integer delta))
  | List [Atom "skew"; target; source; factor] ->
    GuardMemoryAffineReindex.MemoryReindexSkew
      (natural (small target),natural (small source),GuardMemoryNumbers.import_integer (integer factor))
  | List [Atom "reflect"; position] ->
    GuardMemoryAffineReindex.MemoryReindexReflect (natural (small position))
  | _ -> invalid_arg "affine index-map step"

(* This proposal adjustment is untrusted. The checked source loop supplies the
   context position of its entry lower bound. The validator checks every result. *)
let adapt_started_candidate request candidate =
  match request.GuardMemoryUnifiedCompiler.request_source_loop with
  | Some (L.Loop (L.Var lower,_,_)) ->
      let lower = GuardMemoryScheduleInput.natural_size lower in
      let rec statement depth = function
        | L.Loop (L.Constant zero,L.Var upper,body)
          when Z.equal (GuardMemoryNumbers.export_integer zero) Z.zero &&
               GuardMemoryScheduleInput.natural_size upper = depth ->
            L.Loop (L.Var (GuardMemoryCandidate.natural (lower+depth)),L.Var upper,statement (depth+1) body)
        | L.Loop (first,last,body) -> L.Loop (first,last,statement (depth+1) body)
        | L.Guard (test,body) -> L.Guard (test,statement depth body)
        | L.Seq statements -> L.Seq (sequence depth statements)
        | instruction -> instruction
      and sequence depth = function
        | L.SNil -> L.SNil
        | L.SCons (first,rest) -> L.SCons (statement depth first,sequence depth rest) in
      statement 0 candidate
  | _ -> candidate

let propose request =
  let instructions = request.GuardMemoryUnifiedCompiler.request_instructions in
  let dimensions = GuardMemoryScheduleInput.natural_size request.GuardMemoryUnifiedCompiler.request_coordinates in
  let arity = GuardMemoryScheduleInput.natural_size request.GuardMemoryUnifiedCompiler.request_context_arity in
  try
    let syntax = match Lazy.force GuardMemoryCandidate.template with
      | Some (GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "started";
          GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "per-axis"; syntax]]) ->
          if not request.GuardMemoryUnifiedCompiler.request_per_axis_bounds ||
             request.GuardMemoryUnifiedCompiler.request_runtime_versions ||
             request.GuardMemoryUnifiedCompiler.request_guard_prefilter ||
             request.GuardMemoryUnifiedCompiler.request_source_loop = None then
            invalid_arg "started candidate requires a checked source loop";
          Some syntax
      | Some (GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "prefilter";
          GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "versions";
            GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "per-axis"; syntax]]]) ->
          if not (request.GuardMemoryUnifiedCompiler.request_per_axis_bounds &&
                  request.GuardMemoryUnifiedCompiler.request_runtime_versions &&
                  request.GuardMemoryUnifiedCompiler.request_guard_prefilter) ||
             request.GuardMemoryUnifiedCompiler.request_source_loop <> None then
            invalid_arg "prefilter family requires a checked parameter source package";
          Some syntax
      | Some (GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "versions";
          GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "per-axis"; syntax]]) ->
          if not (request.GuardMemoryUnifiedCompiler.request_per_axis_bounds &&
                  request.GuardMemoryUnifiedCompiler.request_runtime_versions) ||
             request.GuardMemoryUnifiedCompiler.request_guard_prefilter ||
             request.GuardMemoryUnifiedCompiler.request_source_loop <> None then
            invalid_arg "version family requires a checked parameter source package";
          Some syntax
      | Some (GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "per-axis"; syntax]) ->
          if not request.GuardMemoryUnifiedCompiler.request_per_axis_bounds ||
             request.GuardMemoryUnifiedCompiler.request_runtime_versions ||
             request.GuardMemoryUnifiedCompiler.request_guard_prefilter ||
             request.GuardMemoryUnifiedCompiler.request_source_loop <> None then
            invalid_arg "per-axis candidate requires a checked vector source package";
          Some syntax
      | syntax -> if request.GuardMemoryUnifiedCompiler.request_per_axis_bounds ||
                     request.GuardMemoryUnifiedCompiler.request_runtime_versions ||
                     request.GuardMemoryUnifiedCompiler.request_guard_prefilter ||
             request.GuardMemoryUnifiedCompiler.request_source_loop <> None then None else syntax in
    match syntax with
    | Some (GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "schedule";
             GuardMemoryCandidate.List axes; GuardMemoryCandidate.List steps]) ->
      if List.length steps > 32 then invalid_arg "schedule index-map limit";
      Some (GuardMemoryUnifiedCompiler.GuardedScheduleCandidate
        (GuardMemoryScheduleInput.instantiate dimensions arity instructions axes,List.map affine_step steps))
    | Some (GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "schedule-list";
             GuardMemoryCandidate.List schedules; GuardMemoryCandidate.List steps]) ->
      if List.length steps > 32 then invalid_arg "schedule index-map limit";
      Some (GuardMemoryUnifiedCompiler.GuardedScheduleCandidate
        (GuardMemoryScheduleInput.explicit schedules,List.map affine_step steps))
    | Some (GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "map-index";
             GuardMemoryCandidate.List steps; syntax]) ->
      if List.length steps > 32 then invalid_arg "affine index-map composition limit";
      Some (GuardMemoryUnifiedCompiler.GuardedMappedCandidate
        (adapt_started_candidate request (GuardMemoryCandidate.instantiate_at instructions None syntax),List.map affine_step steps))
    | Some (GuardMemoryCandidate.List [GuardMemoryCandidate.Atom "tile"; rows; columns]) ->
      Some (GuardMemoryUnifiedCompiler.GuardedTilingCandidate
        (GuardMemoryNumbers.import_integer (GuardMemoryCandidate.integer rows),
         GuardMemoryNumbers.import_integer (GuardMemoryCandidate.integer columns)))
    | _ -> match GuardMemoryCandidate.propose_template instructions syntax with
      | Some (candidate,swaps) -> Some (GuardMemoryUnifiedCompiler.GuardedAffineCandidate (adapt_started_candidate request candidate,swaps))
      | None -> None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
