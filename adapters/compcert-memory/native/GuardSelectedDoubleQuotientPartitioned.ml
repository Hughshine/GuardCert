(* The fallback policy is a function of the current program, not phase-call
   history. Accepted proposals remain checked by the extracted compiler. *)
include GuardSelectedDoubleQuotientCoordinates

let rec original_reduction program source =
  match GuardMemoryDoubleReductionNestData.checked_double_reduction_raw_nest program [] source with
  | Some description -> Some (source,description)
  | None ->
    match source with
    | Clight.Ssequence (capture,Clight.Sifthenelse (Clight.Etempvar (flag,_),
        Clight.Ssequence (_,restore),fallback)) ->
      (match original_reduction program fallback with
       | Some (original,description) ->
         (match List.find_opt (fun id -> id <> flag) (GuardSelectedDoubleCandidate.assigned_temps capture) with
          | Some cache ->
            let limit = ReductionDoubleRegionFactory.reduction_double_limit description in
            if capture = GuardMemoryLongRangeCapture.memory_long_range_capture
                description.GuardMemoryDoubleReductionNestData.reduction_nest_header cache flag limit &&
              restore = GuardMemoryDoubleReductionNestExitCode.double_reduction_exit_code
                description.GuardMemoryDoubleReductionNestData.reduction_nest_iterators cache
            then Some (original,description) else None
          | None -> None)
       | None -> None)
    | _ -> None

let quotient_source program = function
  | Clight.Ssequence (capture,Clight.Sifthenelse (Clight.Etempvar (flag,_),
      Clight.Ssequence ((Clight.Sset (quotient,_) as quotient_capture),
        Clight.Ssequence (_,restore)),fallback)) ->
    (match original_reduction program fallback with
     | Some (original,description) ->
       (match List.find_opt (fun id -> id <> flag) (GuardSelectedDoubleCandidate.assigned_temps capture) with
        | Some cache ->
          let limit = ReductionDoubleRegionFactory.reduction_double_limit description in
          if capture = GuardMemoryLongRangeCapture.memory_long_range_capture
              description.GuardMemoryDoubleReductionNestData.reduction_nest_header cache flag limit &&
            restore = GuardMemoryDoubleReductionNestExitCode.double_reduction_exit_code
              description.GuardMemoryDoubleReductionNestData.reduction_nest_iterators cache &&
            (match GuardMemoryDoubleQuotientLowering.compile_double_ceil_capture cache quotient limit (divisor ()) with
             | Some (expected,_) -> expected = quotient_capture | None -> false)
          then Some (original,description) else None
        | None -> None)
     | None -> None)
  | _ -> None

let signature before = Marshal.to_string before [Marshal.No_sharing]
let source_signature description =
  let request = GuardMemoryDoubleReductionNestEntry.double_reduction_pipeline_request description in
  match GuardMemoryDoublePolyhedral.DoubleAssignmentExtractor.extractor request with
  | Result.Err _ -> None
  | Result.Okk model -> Option.map signature (GuardMemoryDoubleUniformPrepared.export_double_uniform_model model)

let fallback_phase program =
  let rec collect source = match quotient_source program source with
    | Some (_,description) -> (match source_signature description with Some key -> [key] | None -> [])
    | None -> (match source with
      | Clight.Ssequence (a,b) | Clight.Sloop (a,b) | Clight.Sifthenelse (_,a,b) -> collect a @ collect b
      | Clight.Slabel (_,body) -> collect body
      | Clight.Sswitch (_,cases) -> collect_cases cases
      | _ -> [])
  and collect_cases = function
    | Clight.LSnil -> []
    | Clight.LScons (_,body,rest) -> collect body @ collect_cases rest in
  let protected = List.fold_left (fun keys (_,definition) -> match definition with
    | AST.Gfun (Ctypes.Internal fn) -> keys @ collect fn.Clight.fn_body
    | _ -> keys) [] program.Ctypes.prog_defs |> List.sort_uniq String.compare in
  Printf.eprintf "GUARDCERT_QUOTIENT_PARTITION protected_models=%d\n%!" (List.length protected);
  fun before ->
    if List.mem (signature before) protected then (
      Printf.eprintf "GUARDCERT_QUOTIENT_FALLBACK_SKIP already_versioned_source=true\n%!";
      Result.Err "source model is already versioned by the quotient pass")
    else GuardSelectedDoubleQuotientCoordinates.phase before

let rec reduction_kinds program source =
  match quotient_source program source with
  | Some _ -> 1,0
  | None -> if GuardSelectedReductionCandidate.reduction_guard program source then 0,1
    else match source with
    | Clight.Ssequence (a,b) | Clight.Sloop (a,b) | Clight.Sifthenelse (_,a,b) ->
      let qa,oa = reduction_kinds program a in
      let qb,ob = reduction_kinds program b in qa+qb,oa+ob
    | Clight.Slabel (_,body) -> reduction_kinds program body
    | Clight.Sswitch (_,cases) -> reduction_case_kinds program cases
    | _ -> 0,0
and reduction_case_kinds program = function
  | Clight.LSnil -> 0,0
  | Clight.LScons (_,body,rest) ->
      let qa,oa = reduction_kinds program body in
      let qb,ob = reduction_case_kinds program rest in qa+qb,oa+ob

let trace_clight program =
  GuardSelectedDoubleQuotientCoordinates.trace_clight program;
  let original,initialized,quotient,older = List.fold_left
    (fun (original,initialized,quotient,older) (_,definition) -> match definition with
     | AST.Gfun (Ctypes.Internal fn) ->
         let q,o = reduction_kinds program fn.Clight.fn_body in
         original+GuardOriginalMatmulRawCandidate.guarded_statement fn.Clight.fn_body,
         initialized+GuardSelectedDoubleCandidate.initialized_count program fn.Clight.fn_body,
         quotient+q,older+o
     | _ -> original,initialized,quotient,older) (0,0,0,0) program.Ctypes.prog_defs in
  Printf.eprintf "GUARDCERT_DOUBLE_INSTALLED original=%d initialized=%d regions=%d pipeline_calls=%d reduction=%d\n%!"
    original initialized (original+initialized+quotient+older) !GuardSelectedDoubleCandidate.calls (quotient+older);
  Printf.eprintf "GUARDCERT_DOUBLE_TILING_INSTALLED reduction=%d phase_calls=%d adaptations=%d enabled=%b\n%!"
    (quotient+older) !calls !adaptations (enabled ());
  Printf.eprintf "GUARDCERT_QUOTIENT_TILING_INSTALLED regions=%d older_reduction_regions=%d divisor=%s\n%!"
    quotient older (integer_text (divisor ()))
