(* Diagnostic proposal returns the original checked data unchanged. Its staged
   checks never authorize installation; the existing root still validates it. *)
include GuardSelectedDoublePieceIntegerCoverageV5
module V = GuardMemoryDoublePolyhedral.DoubleAssignmentValidator

let propose model actual =
  match GuardSelectedDoublePieceIntegerCoverageV5.propose model actual with
  | None -> None
  | Some (groups,_) as answer ->
      if Sys.getenv_opt "GUARDCERT_PHASE_KIND"=Some "tiled" then begin
        let (parents,context),variables=model in
        let (candidates,_),_=actual in
        let count=nat (List.length context) in
        let left=Q.sequence_target parents groups in
        let before=((left,context),variables) in
        let lines=ref ["scope=diagnostic-only";"installation-authorized=false"] in
        let emit_line line=
          lines:= !lines@[line];
          (match !current_path with None->() | Some path->
            emit (Filename.concat path "piece-order-stages.txt")
              (String.concat "\n" !lines ^ "\n")) in
        let check label action=
          emit_line ("start=" ^ label);
          let start=Unix.gettimeofday () in
          let accepted=checked_bool (action ()) in
          emit_line (Printf.sprintf "end=%s accepted=%b seconds=%.6f" label accepted (Unix.gettimeofday () -. start));
          accepted in
        let wf1=check "retimed-wf" (fun ()->V.check_wf_polyprog before) in
        let wf2=check "actual-wf" (fun ()->V.check_wf_polyprog actual) in
        let same=check "EqDom" (fun ()->V.coq_EqDom before actual) in
        let extended=V.compose_pinstrs_ext_at count left candidates in
        emit_line (Printf.sprintf "valid-access=%b" (V.check_valid_access extended));
        emit_line (Printf.sprintf "static-wf-and-EqDom=%b" (wf1 && wf2 && same));
        let indexed=List.rev (List.mapi (fun index instruction->index,instruction) extended) in
        let rec pairs = function
          | []->true
          | (index,instruction)::rest->
              let self=check (Printf.sprintf "pair-%d-%d" index index)
                (fun ()->V.validate_two_instrs instruction instruction count) in
              let others=List.for_all (fun (other,target)->
                check (Printf.sprintf "pair-%d-%d" index other)
                  (fun ()->V.validate_two_instrs instruction target count) &&
                check (Printf.sprintf "pair-%d-%d" other index)
                  (fun ()->V.validate_two_instrs target instruction count)) rest in
              self && others && pairs rest in
        ignore (pairs indexed)
      end;
      answer
