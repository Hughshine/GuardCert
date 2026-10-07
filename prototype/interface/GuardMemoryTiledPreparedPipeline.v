From Stdlib Require Import List Bool ZArith.
From polcert.src Require Import OpenScop TilingWitness.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemoryScalarLoops GuardMemoryScalarChecker GuardMemoryExtractedTiling.
From GuardInterface Require Import GuardMemoryPreparedPipeline.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Phase producers return data. Checked affine import precedes checked tiling;
    the candidate is actual prepared codegen over the current point space. *)
Definition checked_memory_tiled_prepared_phase
    (phase : OpenScop -> result (OpenScop * OpenScop * list statement_tiling_witness))
    (source : MP.t) : Base.imp (option (GuardMemoryIRs.Loop.t * list statement_tiling_witness)) :=
  match export_memory_model source with
  | None => pure None
  | Some before => match phase before with
    | Err _ => pure None
    | Okk (mid_scop,after_scop,witnesses) =>
      match MP.from_openscop_like_source source mid_scop with
      | Err _ => pure None
      | Okk middle => BIND affine_ok <- GuardMemoryValidator.validate source middle -;
        if affine_ok then
          match GuardMemoryTilingValidator.import_canonical_tiled_after_poly middle after_scop witnesses with
          | Err _ => pure None
          | Okk tiled => BIND tiling_ok <- GuardMemoryTilingValidator.checked_tiling_validate_poly middle tiled witnesses -;
            if tiling_ok then
              BIND generated <- MemoryPrepared.PrepareCore.prepared_codegen (MP.current_view_pprog tiled) -;
              pure (Some (generated,witnesses))
            else pure None end
        else pure None end end end.

Theorem checked_memory_tiled_prepared_phase_correct phase source generated witnesses initial final :
  mayReturn (checked_memory_tiled_prepared_phase phase source) (Some (generated,witnesses)) ->
  GuardMemoryIRs.Loop.semantics generated initial final ->
  MP.instance_list_semantics source initial final.
Proof.
  unfold checked_memory_tiled_prepared_phase.
  destruct (export_memory_model source) as [before|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (phase before) as [[[mid_scop after_scop] ws]|message];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (MP.from_openscop_like_source source mid_scop) as [middle|message];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN affine_ok AFFINE.
  destruct affine_ok; [|apply mayReturn_pure in RUN; discriminate].
  destruct (GuardMemoryTilingValidator.import_canonical_tiled_after_poly middle after_scop ws) as [tiled|message];
    [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN tiling_ok TILING.
  destruct tiling_ok; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN code CODE.
  apply mayReturn_pure in RUN; inversion RUN; subst code ws.
  intro EXEC.
  pose proof (GuardMemoryTilingValidator.checked_tiling_validate_poly_implies_wf_after _ _ _ TILING) as WF.
  pose proof (MemoryPrepared.PrepareCore.prepared_codegen_correct_general _ _ _ _ CODE WF EXEC) as TILED.
  apply guarded_memory_validate_refines with (candidate:=middle); [exact AFFINE|].
  apply guarded_memory_checked_tiling_refines with (candidate:=tiled) (witnesses:=witnesses); assumption.
Qed.

Definition checked_memory_tiled_prepared_loop phase (source : GuardMemoryIRs.Loop.t) :=
  match MemoryPrepared.Extractor.extractor source with
  | Err _ => pure None
  | Okk model => checked_memory_tiled_prepared_phase phase model end.

Theorem checked_memory_tiled_prepared_loop_correct phase source generated witnesses initial final :
  mayReturn (checked_memory_tiled_prepared_loop phase source) (Some (generated,witnesses)) ->
  GuardMemoryIRs.Loop.semantics generated initial final ->
  GuardMemoryIRs.Loop.semantics source initial final.
Proof.
  unfold checked_memory_tiled_prepared_loop.
  destruct (MemoryPrepared.Extractor.extractor source) as [model|message] eqn:EXTRACT;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intros RUN EXEC.
  pose proof (@checked_memory_tiled_prepared_phase_correct phase model generated witnesses initial final RUN EXEC) as MODEL.
  destruct (MemoryPrepared.Extractor.extractor_correct _ _ _ _ EXTRACT MODEL) as [result [SOURCE SAME]].
  unfold GuardMemoryIRs.State.eq,GuardMemoryInstr.State.eq in SAME; subst result; exact SOURCE.
Qed.

(** Installation needs forward execution, in addition to pipeline refinement.
    Re-extract the actual generated Loop, attach the supplied point witness and
    check its alignment/equivalence. No fixed target loop is reconstructed. *)
Definition checked_memory_scalar_generated_tiling axes cap scalars instructions context arrays candidate witnesses :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_extracted_tiling_loops
    (memory_scalar_assumed_loop axes cap scalars (memory_scalar_rectangle 0 axes scalars instructions),context,vars)
    (memory_scalar_assumed_loop axes cap scalars candidate,context,vars) witnesses.

Theorem checked_memory_scalar_generated_tiling_correct axes cap scalars instructions context arrays candidate witnesses :
  mayReturn (checked_memory_scalar_generated_tiling axes cap scalars instructions context arrays candidate witnesses) true ->
  memory_scalar_candidate_certificate axes cap scalars instructions context candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  apply memory_scalar_assumed_execution with (dimensions:=axes) (cap:=cap) (scalars:=scalars); [exact WITHIN|].
  pose proof (@validated_memory_extracted_tiling_loops_at
    (memory_scalar_assumed_loop axes cap scalars (memory_scalar_rectangle 0 axes scalars instructions))
    (memory_scalar_assumed_loop axes cap scalars candidate) context
    (map (fun array => (array,tt)) (context++arrays)) witnesses (rev parameters) before after
    ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply VALID.
  apply memory_scalar_assumed_execution; assumption.
Qed.

Print Assumptions checked_memory_tiled_prepared_phase_correct.
Print Assumptions checked_memory_tiled_prepared_loop_correct.
Print Assumptions checked_memory_scalar_generated_tiling_correct.
