(* Ordinary source metadata and candidate proposals. The request contains the
   actual checked recursive affine source, including parameterized/nonrectangular
   bounds. No rectangular surrogate or handwritten target is substituted. *)
include GuardRankedMultiTensorPipelineCandidate
module Request = AffineNestCheckedCompiler
module Evidence = AffineNestCandidateEvidence

let configured_integer name fallback =
  let value=Option.value (Sys.getenv_opt name) ~default:fallback in
  if String.length value>128 then invalid_arg "affine range policy integer";
  GuardMemoryNumbers.import_integer (Z.of_string value)

let describe live pool source = try
  let policy={
    AffineNestRangeProposal.affine_policy_root_floor=configured_integer "GUARDCERT_AFFINE_FLOOR" "-4";
    affine_policy_root_cap=configured_integer "GUARDCERT_AFFINE_CAP" "8";
    affine_policy_bound_lower=configured_integer "GUARDCERT_AFFINE_BOUND_LOW" "-8";
    affine_policy_bound_upper=configured_integer "GUARDCERT_AFFINE_BOUND_HIGH" "9";
    affine_policy_address_lower=configured_integer "GUARDCERT_AFFINE_ADDRESS_LOW" "-32";
    affine_policy_address_upper=configured_integer "GUARDCERT_AFFINE_ADDRESS_HIGH" "33" } in
  AffineNestMultiProposal.affine_reserve_multi_scans
    (AffineNestRangeProposal.affine_source_range_proposal policy) live pool source
  with Invalid_argument _|Failure _|Stack_overflow -> None

let rec instructions = function
  | L.Instr(instruction,_) -> [instruction]
  | L.Loop(_,_,body)|L.Guard(_,body) -> instructions body
  | L.Seq sequence -> sequence_instructions sequence
and sequence_instructions = function
  | L.SNil -> []
  | L.SCons(head,tail) -> instructions head @ sequence_instructions tail

let calls=ref 0
let propose request =
  if mode()="disabled" then None else
  let path=ref None in
  try
    incr calls;
    let directory=Filename.concat(root())
      (Printf.sprintf "guardcert-affine-phase-%d-%d"(Unix.getpid())!calls) in
    mkdir directory;
    let directory=if Filename.is_relative directory then Filename.concat(Sys.getcwd())directory else directory in
    path:=Some directory;
    let rank=List.length request.Request.affine_requested_axes in
    let code=request.Request.affine_requested_loop in
    let context=request.Request.affine_requested_context in
    let pointers=request.Request.affine_requested_pointers in
    let source=((code,context),List.map(fun id->id,())(context @ pointers)) in
    let source_instructions=instructions code in
    if rank<=0 || source_instructions=[] then invalid_arg "empty affine source";
    emit(Filename.concat directory "source.loop")(statement "" code);
    emit(Filename.concat directory "source-rank.txt")(string_of_int rank^"\n");
    emit(Filename.concat directory "source-origin.txt")"checked-affine-request\nrectangular-surrogate=false\n";
    emit(Filename.concat directory "context.txt")
      (String.concat "\n"(List.map(fun id->Z.to_string(GuardMemoryNumbers.export_positive id))context)^"\n");
    let model=get(P.MemoryPrepared.Extractor.extractor source) in
    let before=Option.get(P.export_memory_model model) in
    let ((middle,after),witnesses)=get(run_rank rank directory before) in
    let mid=get(MP.from_openscop_like_source model middle) in
    require "affine"(force(GuardMemoryPolyhedral.GuardMemoryValidator.validate model mid));
    emit(Filename.concat directory "affine-result.txt")"accepted\n";
    let tiled=get(GuardMemoryPolyhedral.GuardMemoryTilingValidator.import_canonical_tiled_after_poly mid after witnesses) in
    require "tiling"(force(GuardMemoryPolyhedral.GuardMemoryTilingValidator.checked_tiling_validate_poly mid tiled witnesses));
    emit(Filename.concat directory "tiling-result.txt")"accepted\n";
    let ((items,parameters),variables)=MP.current_view_pprog tiled in
    if List.length items<>List.length source_instructions then invalid_arg "statement count changed";
    let generated=List.mapi(fun index item->
      let result,alarm_free=force(P.MemoryPrepared.PrepareCore.prepared_codegen(([item],parameters),variables)) in
      if not alarm_free then failwith "prepared codegen alarmed";
      let body=fst(fst result) in
      emit(Filename.concat directory(Printf.sprintf "raw-statement-%d.loop"index))(statement "" body);body)items in
    let raw=L.Seq(List.fold_right(fun head tail->L.SCons(head,tail))generated L.SNil) in
    emit(Filename.concat directory "raw-generated.loop")(statement "" raw);
    let has_tiles=List.exists(fun witness->witness.TilingWitness.stw_links<>[])witnesses in
    let units=if has_tiles then unit_axes_ranked rank witnesses else List.init rank(fun _->false) in
    let all_unit=has_tiles && List.for_all Fun.id units in
    let partial=has_tiles && not all_unit && List.exists Fun.id units in
    let completed=if partial then complete_ranked_units rank units raw else raw in
    emit(Filename.concat directory "completed.loop")(statement "" completed);
    let candidate=adapt_bounds completed in
    emit(Filename.concat directory "generated.loop")(statement "" candidate);
    let kind=if all_unit || not has_tiles then "mapped" else "tiled" in
    let evidence=if kind="mapped" then match reindex_ranked rank candidate with
      | Some steps -> Evidence.AffineIndexEvidence steps
      | None -> invalid_arg "generated affine reindex refused"
      else Evidence.AffineTilingEvidence witnesses in
    if Sys.getenv_opt "GUARDCERT_PIPELINE_CHECK_DIAGNOSTICS"=Some "1" then begin
      let valid,free=force(Evidence.checked_affine_candidate
        request.Request.affine_requested_bounds code context pointers candidate evidence) in
      emit(Filename.concat directory "whole-candidate-check-diagnostic.txt")
        (Printf.sprintf "valid=%b\nalarm-free=%b\n"valid free)
    end;
    emit(Filename.concat directory "receipt.txt")
      ("source=checked-affine-request\naffine-validation=accepted\ntiling-validation=accepted\nprepared-codegen=successful\nprepared-codegen-scope=per-statement\nstatement-distribution=proposed\nwhole-candidate-factory-check=pending\ncandidate-kind="^kind^"\n");
    Some(candidate,evidence)
  with Invalid_argument reason|Failure reason|Sys_error reason ->
    Option.iter(fun directory->emit(Filename.concat directory "refusal.txt")(reason^"\n"))!path;
    None
  | Stack_overflow ->
    Option.iter(fun directory->emit(Filename.concat directory "refusal.txt")"stack overflow\n")!path;
    None
