(* Untrusted proposals reuse the real OpenScop/Pluto transport. The extracted
   checker remains authoritative. Diagnostics recognize literal checked guards. *)
let schedule = GuardSelectedDoubleCandidate.schedule
let swaps = GuardSelectedDoubleCandidate.swaps
let private_count = GuardSelectedDoubleCandidate.private_count
let reduction_guard program = function
  | Clight.Ssequence (capture,Clight.Sifthenelse
      (Clight.Etempvar (flag,_),Clight.Ssequence (_,restore),source)) ->
    (match GuardMemoryDoubleReductionNestData.checked_double_reduction_raw_nest program [] source with
     | Some description ->
       (match List.find_opt (fun id -> id <> flag) (GuardSelectedDoubleCandidate.assigned_temps capture) with
        | None -> false
        | Some cache ->
          let limit = ReductionDoubleRegionFactory.reduction_double_limit description in
          capture = GuardMemoryLongRangeCapture.memory_long_range_capture
            description.GuardMemoryDoubleReductionNestData.reduction_nest_header cache flag limit &&
          restore = GuardMemoryDoubleReductionNestExitCode.double_reduction_exit_code
            description.GuardMemoryDoubleReductionNestData.reduction_nest_iterators cache)
     | _ -> false)
  | _ -> false
let rec reduction_count program source =
  if reduction_guard program source then 1 else match source with
  | Clight.Ssequence (first,second) | Clight.Sloop (first,second) ->
    reduction_count program first + reduction_count program second
  | Clight.Sifthenelse (_,yes,no) -> reduction_count program yes + reduction_count program no
  | Clight.Slabel (_,body) -> reduction_count program body
  | Clight.Sswitch (_,cases) -> reduction_cases program cases
  | _ -> 0
and reduction_cases program = function
  | Clight.LSnil -> 0
  | Clight.LScons (_,body,rest) -> reduction_count program body + reduction_cases program rest
let trace_clight program =
  let original,initialized,reduction = List.fold_left
    (fun (original,initialized,reduction) (_,definition) -> match definition with
    | AST.Gfun (Ctypes.Internal fn) ->
      original + GuardOriginalMatmulRawCandidate.guarded_statement fn.Clight.fn_body,
      initialized + GuardSelectedDoubleCandidate.initialized_count program fn.Clight.fn_body,
      reduction + reduction_count program fn.Clight.fn_body
    | _ -> original,initialized,reduction) (0,0,0) program.Ctypes.prog_defs in
  Printf.eprintf "GUARDCERT_DOUBLE_INSTALLED original=%d initialized=%d regions=%d pipeline_calls=%d reduction=%d\n%!"
    original initialized (original+initialized+reduction) !GuardSelectedDoubleCandidate.calls reduction
