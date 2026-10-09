(* The adapter returns the affine reference for the existing final checker.
   The proved lowering postpass tightens its actual executable loop bounds.
   This receipt computes that same pure extracted postpass before acceptance. *)
include GuardSelectedDoubleMixedAdapter

let rec changed_bounds reference actual = match reference,actual with
  | L.Loop (_,old_upper,old_body),L.Loop (_,new_upper,new_body) ->
      (if old_upper=new_upper then 0 else 1)+changed_bounds old_body new_body
  | L.Guard (_,old_body),L.Guard (_,new_body) -> changed_bounds old_body new_body
  | L.Seq old_sequence,L.Seq new_sequence -> changed_sequence old_sequence new_sequence
  | _ -> 0
and changed_sequence reference actual = match reference,actual with
  | L.SCons (old_head,old_tail),L.SCons (new_head,new_tail) ->
      changed_bounds old_head new_head+changed_sequence old_tail new_tail
  | _ -> 0

let adapt caps input =
  match GuardSelectedDoubleMixedAdapter.adapt caps input with
  | Result.Err message -> Result.Err message
  | Result.Okk (((reference,context),variables) as candidate) ->
      let actual = GuardMemoryDoubleTightenedCandidate.double_rectangular_tightened_loop caps reference in
      let changed = changed_bounds reference actual in
      (match !current_path with
       | Some path ->
           emit (Filename.concat path "runtime-tightened.loop") (statement "" actual);
           emit (Filename.concat path "runtime-tightening.txt")
             (Printf.sprintf "changed-bounds=%d\nreference-check=pending\nactual-postpass=extracted-verified-function\n" changed)
       | None -> ());
      Printf.eprintf "GUARDCERT_RUNTIME_BOUNDS changed=%d reference-check=pending\n%!" changed;
      Result.Okk candidate
