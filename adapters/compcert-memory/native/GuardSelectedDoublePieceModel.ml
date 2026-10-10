(* Actual model-level C_opt diagnostics. Groups, coordinate maps and coverage
   trees are untrusted proposals. The extracted checker binds them to the
   source/candidate models. Whole-program installation still uses its old root. *)
include GuardSelectedDoublePieceActions
module Q = GuardMemoryDoublePieceExecution.DoublePieceSequence
module R = GuardMemoryDoublePieceParameterDomains.DoublePieceParameterDomains
module M = GuardMemoryDoublePieceModel

let rec sequence_witness = function
  | PF.D.CoverPiece index -> Q.Single.S.F.D.CoverPiece index
  | PF.D.CoverEmpty -> Q.Single.S.F.D.CoverEmpty
  | PF.D.CoverSplit (row,yes,no) ->
    Q.Single.S.F.D.CoverSplit (row,sequence_witness yes,sequence_witness no)
let replace_head replacement = function
  | []->invalid_arg "empty model mutation"
  | _::rest->replacement::rest

let model_diagnose intervals source candidate =
  let path=match !current_path with Some path->path | None->failwith "missing model diagnostic path" in
  let receipt=Filename.concat path "piece-model-diagnostic.txt" in
  let lines=ref ["scope=actual-model-conditional-execution";"whole-fusion-installed=false"] in
  let record text=lines:= !lines@[text];emit receipt (String.concat "\n" !lines ^ "\n") in
  try
    let original=match E.extractor source with Result.Okk model->model | Result.Err reason->failwith reason in
    let actual=match E.extractor candidate with Result.Okk model->model | Result.Err reason->failwith reason in
    let data=match !saved_phase with Some data->data | None->failwith "missing actual phase" in
    let retained=checked_value (GuardMemoryDoubleRetainedPhase.checked_double_retained_phase
      (fun _->Result.Okk data) original) in
    let model=match retained with Some (Some ((_,model),_))->record "retained-forward-phase=true";model
      | _->failwith "retained checked phase refused" in
    let (parents,context),variables=model in
    let (candidates,candidate_context),candidate_variables=actual in
    if context<>candidate_context || variables<>candidate_variables then invalid_arg "candidate model declarations differ";
    let parameters=List.length context in
    let count=nat parameters in
    let guards=prefix_facts parameters intervals in
    let restricted_parents=R.piece_restrict_program count guards parents in
    let restricted_candidates=R.piece_restrict_program count guards candidates in
    record (Printf.sprintf "source-instructions=%d\ncandidate-pieces=%d" (List.length parents) (List.length candidates));
    let assignments=List.mapi (fun index candidate->
      let parent,source=List.mapi (fun index source->index,source) restricted_parents |>
        List.find (fun (_,source)->I.eqb source.P.pi_instr candidate.P.pi_instr) in
      let proposal=propose parameters intervals source candidate in
      let piece={proposal with PC.piece_domain=candidate.P.pi_poly} in
      emit (Filename.concat path (Printf.sprintf "piece-model-%d.json" index))
        (Printf.sprintf "{\"piece\":%d,\"parent\":%d,\"candidate_depth\":%d,\"source_depth\":%d,\"parameter_facts\":%s,\"source_domain\":%s,\"candidate_domain\":%s,\"embed\":%s,\"project\":%s,\"candidate_arguments\":%s,\"source_arguments\":%s,\"actual_schedule\":%s,\"retimed_schedule\":%s}\n"
          index parent (IO.nat_to_int candidate.P.pi_depth) (IO.nat_to_int source.P.pi_depth)
          (json_rows guards) (json_rows source.P.pi_poly) (json_rows candidate.P.pi_poly)
          (json_rows piece.PC.piece_embed) (json_rows piece.PC.piece_project)
          (json_rows candidate.P.pi_transformation) (json_rows source.P.pi_transformation)
          (json_rows candidate.P.pi_schedule) (json_rows (Q.Single.A.piece_retimed_instruction source candidate piece).P.pi_schedule));
      parent,(candidate,piece)) restricted_candidates in
    let groups=List.mapi (fun parent _->List.filter_map
      (fun (id,item)->if id=parent then Some item else None) assignments) restricted_parents in
    if List.map fst (List.concat groups)<>restricted_candidates then invalid_arg "candidate pieces do not follow grouped source ordinals";
    let witnesses=List.map2 (fun source items->
      coverage source.P.pi_poly (List.map (fun (_,piece)->PC.piece_image_domain piece) items) |>
      sequence_witness) restricted_parents groups in
    let accepted=checked_bool (M.check_double_piece_model guards model actual groups witnesses) in
    record (Printf.sprintf "actual-model-execution-check=%b" accepted);
    let first=List.hd groups in
    let omitted=replace_head (List.tl first) groups in
    let duplicated=replace_head (List.hd first::first) groups in
    record (Printf.sprintf "omitted-piece-refused=%b\nduplicated-piece-refused=%b"
      (not (checked_bool (M.check_double_piece_model guards model actual omitted witnesses)))
      (not (checked_bool (M.check_double_piece_model guards model actual duplicated witnesses))));
    let first_candidate=List.hd candidates in
    let other=List.find (fun pi->not (I.eqb pi.P.pi_instr first_candidate.P.pi_instr)) parents in
    let wrong_instruction={first_candidate with P.pi_instr=other.P.pi_instr} in
    let changed=replace_head wrong_instruction candidates in
    record (Printf.sprintf "actual-instruction-refused=%b"
      (not (checked_bool (M.check_double_piece_model guards model ((changed,candidate_context),candidate_variables) groups witnesses))));
    let reversed=List.map (fun pi->{pi with P.pi_schedule=reversed_schedule pi.P.pi_schedule}) candidates in
    record (Printf.sprintf "actual-reversed-dependence-refused=%b"
      (not (checked_bool (M.check_double_piece_model guards model ((reversed,candidate_context),candidate_variables) groups witnesses))));
    record "diagnostic=completed"
  with (Invalid_argument _ | Failure _ | Not_found | Sys_error _) as error->
    record ("diagnostic=refused reason=" ^ Printexc.to_string error)

let adapt intervals source raw =
  let answer=GuardSelectedDoubleTreeSpecializedCoordinates.adapt intervals source raw in
  (match answer with Result.Okk candidate->model_diagnose intervals source candidate | Result.Err _->());
  answer
