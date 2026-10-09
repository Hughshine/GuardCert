(* Proposal policies and compiler observations only. The extracted factory
   checks the actual source, footprints, candidate and installation. *)
include GuardSelectedDoubleQuotientPartitioned
module Parent = GuardSelectedDoubleQuotientPartitioned

let header_quotient_source program = function
  | Clight.Ssequence (capture,Clight.Sifthenelse (Clight.Etempvar (flag,_),
      Clight.Ssequence ((Clight.Sset (quotient,_) as quotient_capture),
        Clight.Ssequence (_,restore)),fallback)) ->
    (match GuardMemoryDoubleReductionNestData.checked_double_reduction_raw_nest program [] fallback,
      GuardMemoryDoubleHeaderNestData.checked_double_header_raw_nest program [] fallback with
     | None,Some description ->
       (match List.find_opt (fun id -> id <> flag) (GuardSelectedDoubleCandidate.assigned_temps capture) with
        | Some cache ->
          let limit = HeaderDoubleQuotientFactory.header_double_limit description in
          if capture = GuardMemoryLongRangeCapture.memory_long_range_capture
              description.GuardMemoryDoubleReductionNestData.reduction_nest_header cache flag limit &&
            restore = GuardMemoryDoubleReductionNestExitCode.double_reduction_exit_code
              description.GuardMemoryDoubleReductionNestData.reduction_nest_iterators cache &&
            (match GuardMemoryDoubleQuotientLowering.compile_double_ceil_capture cache quotient limit (divisor ()) with
             | Some (expected,_) -> expected = quotient_capture | None -> false)
          then Some (fallback,description) else None
        | None -> None)
     | _ -> None)
  | _ -> None

(* The existing quotient pass receives a policy derived from its actual input. *)
let quotient_phase program = Parent.fallback_phase program

let rec kinds program source =
  match header_quotient_source program source,Parent.quotient_source program source with
  | Some _,_ -> 1,0,0
  | _,Some _ -> 0,1,0
  | _ -> if GuardSelectedReductionCandidate.reduction_guard program source then 0,0,1
    else match source with
    | Clight.Ssequence (a,b) | Clight.Sloop (a,b) | Clight.Sifthenelse (_,a,b) ->
      let ha,qa,oa = kinds program a in
      let hb,qb,ob = kinds program b in ha+hb,qa+qb,oa+ob
    | Clight.Slabel (_,body) -> kinds program body
    | Clight.Sswitch (_,cases) -> case_kinds program cases
    | _ -> 0,0,0
and case_kinds program = function
  | Clight.LSnil -> 0,0,0
  | Clight.LScons (_,body,rest) ->
      let ha,qa,oa = kinds program body in
      let hb,qb,ob = case_kinds program rest in ha+hb,qa+qb,oa+ob

let trace_clight program =
  Parent.trace_clight program;
  let original,initialized,header,quotient,older = List.fold_left
    (fun (original,initialized,header,quotient,older) (_,definition) -> match definition with
     | AST.Gfun (Ctypes.Internal fn) ->
       let h,q,o = kinds program fn.Clight.fn_body in
       original+GuardOriginalMatmulRawCandidate.guarded_statement fn.Clight.fn_body,
       initialized+GuardSelectedDoubleCandidate.initialized_count program fn.Clight.fn_body,
       header+h,quotient+q,older+o
     | _ -> original,initialized,header,quotient,older) (0,0,0,0,0) program.Ctypes.prog_defs in
  Printf.eprintf "GUARDCERT_HEADER_QUOTIENT_INSTALLED regions=%d\n%!" header;
  Printf.eprintf "GUARDCERT_DOUBLE_INSTALLED original=%d initialized=%d regions=%d pipeline_calls=%d reduction=%d\n%!"
    original initialized (original+initialized+header+quotient+older)
    !GuardSelectedDoubleCandidate.calls (header+quotient+older);
  Printf.eprintf "GUARDCERT_DOUBLE_TILING_INSTALLED reduction=%d phase_calls=%d adaptations=%d enabled=%b\n%!"
    (header+quotient+older) !calls !adaptations (enabled ());
  Printf.eprintf "GUARDCERT_QUOTIENT_TILING_INSTALLED regions=%d older_reduction_regions=%d divisor=%s\n%!"
    (header+quotient) older (integer_text (divisor ()))
