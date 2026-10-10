(* Typed action, parameter and dependency diagnostics. The old whole-program
   compiler retains installation authority until the program-point bridge is
   connected to its actual factory and host. *)
include GuardSelectedDoublePieceReceipts
module PA = GuardMemoryDoublePieceActions.DoublePieceActions
let checked_value operation =
  let answer=ref None in
  ImpureConfig.Core.Base.bind operation (fun (value,alarm_free)->answer:=Some (value,alarm_free));
  match !answer with Some (value,true)->Some value | _->None
let mutate_bias rows = match List.rev rows with
  | []->invalid_arg "empty action matrix"
  | (row,bias)::rest->List.rev ((row,BinInt.Z.add bias (integer Z.one))::rest)
let mutate_prefix rows = match rows with
  | []->invalid_arg "empty parameter prefix"
  | (row,bias)::rest->(row,BinInt.Z.add bias (integer Z.one))::rest
let reversed_schedule rows = List.map (fun (row,bias)->
  List.map BinInt.Z.opp row,BinInt.Z.opp bias) rows

let action_diagnose intervals source candidate =
  let path=match !current_path with Some path->path | None->failwith "missing action diagnostic path" in
  let receipt=Filename.concat path "piece-action-diagnostic.txt" in
  let lines=ref ["scope=typed-actions-parameters-and-dependence";"whole-fusion-installed=false"] in
  let record text=lines:= !lines@[text];emit receipt (String.concat "\n" !lines ^ "\n") in
  try
    let original=match E.extractor source with Result.Okk model->model | Result.Err reason->failwith reason in
    let extracted=match E.extractor candidate with Result.Okk model->model | Result.Err reason->failwith reason in
    let data=match !saved_phase with Some data->data | None->failwith "missing actual phase" in
    let result=checked_value (GuardMemoryDoubleRetainedPhase.checked_double_retained_phase
      (fun _->Result.Okk data) original) in
    let model=match result with Some (Some ((_,model),_))->record "retained-forward-phase=true";model
      | _->record "retained-forward-phase=false";failwith "retained checked phase refused" in
    let (parents,context),variables=model in
    let (candidates,candidate_context),candidate_variables=extracted in
    if context<>candidate_context || variables<>candidate_variables then invalid_arg "candidate model declarations differ";
    let parameters=List.length context in
    record (Printf.sprintf "source-instructions=%d\ncandidate-pieces=%d" (List.length parents) (List.length candidates));
    let assignments=List.mapi (fun index candidate->
      let parent,source=List.mapi (fun index source->index,source) parents |> List.find (fun (_,source)->I.eqb source.P.pi_instr candidate.P.pi_instr) in
      let piece=propose parameters intervals source candidate in
      let restricted={candidate with P.pi_poly=piece.PC.piece_domain} in
      let accepted=checked_bool (PA.check_piece_actions (nat parameters) source restricted piece) in
      record (Printf.sprintf "piece=%d parent=%d action-and-prefix=%b" index parent accepted);
      let retimed=PA.piece_retimed_instruction source restricted piece in
      emit (Filename.concat path (Printf.sprintf "piece-action-%d.json" index))
        (Printf.sprintf "{\"piece\":%d,\"parent\":%d,\"domain\":%s,\"embed\":%s,\"project\":%s,\"candidate_arguments\":%s,\"source_arguments\":%s,\"actual_schedule\":%s,\"retimed_schedule\":%s,\"source_schedule\":%s}\n"
          index parent (json_rows piece.PC.piece_domain) (json_rows piece.PC.piece_embed)
          (json_rows piece.PC.piece_project) (json_rows restricted.P.pi_transformation)
          (json_rows source.P.pi_transformation) (json_rows restricted.P.pi_schedule)
          (json_rows retimed.P.pi_schedule) (json_rows source.P.pi_schedule));
      source,restricted,piece,retimed) candidates in
    let retimed=List.map (fun (_,_,_,retimed)->retimed) assignments in
    let actual=List.map (fun (_,candidate,_,_)->candidate) assignments in
    let equivalent=checked_bool (GuardMemoryDoublePolyhedral.validate_double_equivalence
      ((retimed,context),variables) ((actual,context),variables)) in
    record (Printf.sprintf "retimed-to-actual-dependence=%b" equivalent);
    let source,candidate,piece,_=List.hd assignments in
    let other=List.find (fun pi->not (I.eqb pi.P.pi_instr candidate.P.pi_instr)) parents in
    let wrong_instruction={candidate with P.pi_instr=other.P.pi_instr} in
    let wrong_arguments={candidate with P.pi_transformation=mutate_bias candidate.P.pi_transformation} in
    let wrong_prefix={piece with PC.piece_embed=mutate_prefix piece.PC.piece_embed} in
    record (Printf.sprintf "wrong-instruction-refused=%b\nwrong-arguments-refused=%b\nwrong-prefix-refused=%b"
      (not (checked_bool (PA.check_piece_actions (nat parameters) source wrong_instruction piece)))
      (not (checked_bool (PA.check_piece_actions (nat parameters) source wrong_arguments piece)))
      (not (checked_bool (PA.check_piece_actions (nat parameters) source candidate wrong_prefix))));
    let reversed=List.map (fun pi->{pi with P.pi_schedule=reversed_schedule pi.P.pi_schedule}) actual in
    let reverse_refused=not (checked_bool (GuardMemoryDoublePolyhedral.validate_double_equivalence
      ((retimed,context),variables) ((reversed,context),variables))) in
    record (Printf.sprintf "reversed-dependence-refused=%b" reverse_refused);
    record "diagnostic=completed"
  with (Invalid_argument _ | Failure _ | Not_found | Sys_error _) as error->
    record ("diagnostic=refused reason=" ^ Printexc.to_string error)

let adapt intervals source raw =
  let answer=GuardSelectedDoublePieceReceipts.adapt intervals source raw in
  (match answer with Result.Okk candidate->action_diagnose intervals source candidate | Result.Err _->());
  answer
