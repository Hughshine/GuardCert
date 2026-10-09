(* Diagnostic executable only. This never supplies compiler certificates or code. *)
let show name value = Printf.printf "%s=%b " name value
let some = Option.is_some
let rec statement_tag = function
  | Clight.Sskip -> "skip" | Clight.Sassign _ -> "assign" | Clight.Sset _ -> "set"
  | Clight.Ssequence (a,b) -> "seq("^statement_tag a^","^statement_tag b^")"
  | Clight.Sloop _ -> "loop" | Clight.Sifthenelse _ -> "if"
  | Clight.Slabel (_,s) -> "label("^statement_tag s^")" | _ -> "other"
let leaf p controls source =
  show "instruction" (some (GuardMemoryDoubleSourceInstruction.checked_double_source_instruction p controls source));
  match GuardMemoryDoubleAssignmentFactory.decode_double_assignment source with
  | None -> show "assignment" false
  | Some assignment ->
    show "assignment" true;
    show "write" (some (GuardMemoryDoubleAffineSourceAccess.checked_double_affine_source_access p controls
      assignment.GuardMemoryDoubleAssignmentFactory.double_assignment_target));
    show "reads" (some (GuardMemoryDoubleAffineSourceAccess.checked_double_affine_source_reads p controls
      assignment.GuardMemoryDoubleAssignmentFactory.double_assignment_reads))
let rec path p controls source =
  match GuardMemoryDoubleInitializedNestData.double_initialized_outer_shape source,
    GuardMemoryDoubleReductionNestData.double_reduction_root_header source with
  | Some (iterator,child),Some _ -> path p (controls@[iterator]) child
  | _ -> Printf.printf "depth=%d shape=%s " (List.length controls) (statement_tag source);
    leaf p controls source
let unwrap = function Errors.OK p -> p | Errors.Error _ -> failwith "frontend normalization refused"
let read path = let channel=open_in_bin path in
  Fun.protect ~finally:(fun ()->close_in channel) (fun ()->really_input_string channel (in_channel_length channel))
let () =
  Frontend.init ();
  Clflags.stdlib_path := Sys.argv.(2);
  Clflags.use_standard_headers := true;
  Clflags.option_flongdouble := true;
  Clflags.option_fstruct_passing := true;
  Clflags.option_fpacked_structs := true;
  let source=Sys.argv.(1) in let preprocessed=Sys.argv.(3) in
  Frontend.preprocess source preprocessed;
  let csyntax=Frontend.parse_c_file source preprocessed in
  let normalized=unwrap (SimplLocals.transf_program (unwrap (SimplExpr.transl_program csyntax))) in
  let chosen=GuardScopFrontend.chosen_labels () in
  let p=DoubleLiteralSelectedNormalization.normalize_selected_double_literals chosen normalized in
  List.iteri (fun index region ->
    Printf.printf "candidate=%d " index;
    show "raw" (some (GuardMemoryDoubleRectangularNestDecoder.checked_double_rectangular_raw_nest p [] region));
    let elided=GuardMemoryDoubleInitializedRawNest.double_initialized_elide_skips region in
    show "canonical" (some (GuardMemoryDoubleRectangularNestDecoder.checked_double_rectangular_nest p [] elided));
    path p [] elided; Printf.printf "\n%!")
    (ClightSelectedRegion.selected_program_candidates chosen p)
