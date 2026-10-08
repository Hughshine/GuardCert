(* A data-only proposal strategy. Whole-model affine/tiling validation precedes
   actual per-statement prepared codegen. The final candidate checker must
   validate the complete composed target; distribution is not assumed valid. *)
include GuardCompletedPreparedTensorCandidate
module P = GuardMemoryPreparedPipeline
module MP = GuardMemoryPreparedPipeline.MP
let force computation =
  let result=ref None in
  ImpureConfig.Core.Base.bind computation(fun value->result:=Some value;());
  match !result with Some value->value|None->failwith "no monadic result"
let get = function Result.Okk value->value|Result.Err _->failwith "model import refused"
let require stage (valid,alarm_free) =
  if not(valid && alarm_free)then failwith(stage^" refused or alarmed")
let propose instructions =
  if mode()="disabled" then None else try
    incr invocations;
    let path=Filename.concat(root())(Printf.sprintf "guardcert-phase-%d-%d"(Unix.getpid())!invocations)in
    mkdir path;
    let path=if Filename.is_relative path then Filename.concat(Sys.getcwd())path else path in
    let arrays=List.sort_uniq compare(List.concat_map(fun instruction ->
      List.map fst(instruction.M.instruction_write::instruction.M.instruction_reads))instructions)in
    let maximum=List.fold_left(fun largest id->Z.max largest(GuardMemoryNumbers.export_positive id))Z.one arrays in
    let context=List.init 5(fun i->GuardMemoryNumbers.import_positive(Z.add maximum(Z.of_int(i+1))))in
    let code=GuardMemoryScalarLoops.memory_scalar_rectangle(nat 0)(nat 3)(nat 2)instructions in
    let source=((code,context),List.map(fun id->id,())(context@arrays))in
    emit(Filename.concat path "source.loop")(statement "" code);
    let model=get(P.MemoryPrepared.Extractor.extractor source)in
    let before=Option.get(P.export_memory_model model)in
    let ((mid,after),witnesses)=get(run path before)in
    let middle=get(MP.from_openscop_like_source model mid)in
    require "affine"(force(GuardMemoryPolyhedral.GuardMemoryValidator.validate model middle));
    emit(Filename.concat path "affine-result.txt")"accepted\n";
    let tiled=get(GuardMemoryPolyhedral.GuardMemoryTilingValidator.import_canonical_tiled_after_poly middle after witnesses)in
    require "tiling"(force(GuardMemoryPolyhedral.GuardMemoryTilingValidator.checked_tiling_validate_poly middle tiled witnesses));
    emit(Filename.concat path "tiling-result.txt")"accepted\n";
    let ((items,parameters),variables)=MP.current_view_pprog tiled in
    if List.length items<>List.length instructions then invalid_arg "source statement count changed";
    let generated=List.mapi(fun index item ->
      let result,alarm_free=force(P.MemoryPrepared.PrepareCore.prepared_codegen(([item],parameters),variables))in
      if not alarm_free then failwith "per-statement codegen alarmed";
      let body=fst(fst result)in
      emit(Filename.concat path(Printf.sprintf "raw-statement-%d.loop"index))(statement ""body);
      body)items in
    let raw=L.Seq(List.fold_right(fun head tail->L.SCons(head,tail))generated L.SNil)in
    emit(Filename.concat path "raw-generated.loop")(statement ""raw);
    let tiled=List.exists(fun w->w.TilingWitness.stw_links<>[])witnesses in
    let units=if tiled then unit_axes witnesses else [false;false;false]in
    let all_unit=tiled && List.for_all Fun.id units in
    let partial=tiled && not all_unit && List.exists Fun.id units in
    let completed=if partial then complete_unit_points units raw else raw in
    emit(Filename.concat path "completed.loop")(statement ""completed);
    let candidate=adapt_bounds completed in
    emit(Filename.concat path "generated.loop")(statement ""candidate);
    let kind=if all_unit || not tiled then "mapped"else"tiled"in
    let proposal=if kind="mapped"then match reindex candidate with
      |Some steps->ClightTensorGeneratedCandidates.TensorGeneratedMapped(candidate,steps)
      |None->invalid_arg "composed affine coordinate reindex refused"
      else ClightTensorGeneratedCandidates.TensorGeneratedTiled(candidate,witnesses)in
    emit(Filename.concat path "receipt.txt")
      ("affine-validation=accepted\ntiling-validation=accepted\nprepared-codegen=successful\nprepared-codegen-scope=per-statement\nstatement-distribution=proposed\nwhole-candidate-check=pending\ncandidate-kind="^kind^"\n");
    Some proposal
  with Invalid_argument _|Failure _|Sys_error _|Stack_overflow->None
