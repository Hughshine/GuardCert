(* Diagnostics realize the existing identity trace primitive and return the
   supplied value unchanged. They observe compilation, not target execution. *)
let enabled () = Sys.getenv_opt "GUARDCERT_PHASE_TRACE" = Some "1"
let current_stage = ref "outside-profiled-phase"
let cpu_seconds () =
  let times = Unix.times () in times.Unix.tms_utime +. times.Unix.tms_stime
let trace _ message value =
  if enabled () && String.starts_with ~prefix:"guardcert-phase/" message then begin
    current_stage := message;
    Printf.eprintf "GUARDCERT_PHASE label=%S wall=%.6f cpu=%.6f\n%!"
      message (Unix.gettimeofday ()) (cpu_seconds ())
  end;
  value
