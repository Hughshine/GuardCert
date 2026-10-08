(* Ordinary adapters reuse the actual Loop pipeline. The private-loaded factory
   independently checks the profile, both range environments and the returned
   mapped/tiling proposal against its own source model and width assumptions. *)
module Source = ClightAffineInnerPointerCandidates
module Bounds = GuardMemoryArrayBackend.MemoryNested.A
module Encoder = GuardMemoryPointerBackend.MemoryFramedNested.N.A

let profile source = try
  let setting=GuardSignedAffinePipelineCandidate.configured_integer in
  Source.propose_affine_inner_pointer_profile
    (setting "GUARDCERT_AFFINE_ROW_CAP" "64")
    (setting "GUARDCERT_AFFINE_COLUMN_CAP" "64")
    (setting "GUARDCERT_AFFINE_GEOMETRY_CAP" "16")
    (setting "GUARDCERT_AFFINE_EXTENT" "8192") source
  with Invalid_argument _|Failure _|Sys_error _|Stack_overflow -> None

let propose request = try
  let caps=request.Source.affine_request_geometry_caps in
  let scalars=List.length request.Source.affine_request_context-List.length caps in
  if scalars<0 then invalid_arg "loaded affine context";
  let z=GuardMemoryNumbers.import_integer in
  let ranges=List.mapi(fun index cap->(z(if index=0 then Z.one else Z.zero),cap))caps @
    List.init scalars(fun _->z(Z.of_string "-2147483648"),z(Z.of_string "2147483647")) in
  let validator=List.map(fun (lower,upper)->{Bounds.lower;upper})ranges in
  let encoder=List.map(fun (lower,upper)->{Encoder.lower;upper})ranges in
  (* Axis pairs configure rank and record source caps. The optimizer receives
     the original nonrectangular Loop, never a rectangular replacement. *)
  let pipeline_request={
    AffineNestCheckedCompiler.affine_requested_loop=request.Source.affine_request_source;
    affine_requested_context=request.Source.affine_request_context;
    affine_requested_bounds=validator;
    affine_requested_pointers=request.Source.affine_request_pointers;
    affine_requested_axes=[z Z.zero,request.Source.affine_request_row_cap;
                           z Z.zero,request.Source.affine_request_column_cap]} in
  let before = !(GuardSignedAffinePipelineCandidate.calls) in
  let result=GuardSignedAffinePipelineCandidate.propose pipeline_request in
  if !(GuardSignedAffinePipelineCandidate.calls) > before then begin
    let directory=Filename.concat(GuardSignedAffinePipelineCandidate.root())
      (Printf.sprintf "guardcert-signed-affine-phase-%d-%d" (Unix.getpid())
        !(GuardSignedAffinePipelineCandidate.calls)) in
    if Sys.file_exists directory then
      GuardSignedAffinePipelineCandidate.emit (Filename.concat directory "request-adapter.txt")
        "private-loaded-affine-request\nsource-model-unchanged=true\nfinal-checker=private-loaded-affine-factory\nconditional-child-load=false\n"
  end;
  match result with
  | None -> None
  | Some(candidate,evidence) ->
    let proposal=match evidence with
      | AffineNestCandidateEvidence.AffineIndexEvidence steps -> Source.AffineInnerMappedProposal(candidate,steps)
      | AffineNestCandidateEvidence.AffineTilingEvidence witnesses -> Source.AffineInnerTilingProposal(candidate,witnesses) in
    Some {Source.affine_proposal_validator_bounds=validator;
          affine_proposal_encoder_bounds=encoder;affine_proposal_candidate=proposal}
  with Invalid_argument _|Failure _|Sys_error _|Stack_overflow -> None
