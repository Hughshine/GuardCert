From Stdlib Require Import List Bool ZArith.
From polcert.src Require Import OpenScop TilingWitness.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleUniformPrepared GuardMemoryDoubleExtractedTiling.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Phase output and bound adaptation are proposals. The phase validators
    check the raw codegen path; the final checker separately checks the actual
    adapted Loop that is lowered and installed. *)
Definition checked_double_tiled_prepared_phase
  (phase : OpenScop -> result (OpenScop * OpenScop * list statement_tiling_witness))
  (source : DoubleAssignmentIRs.PolyLang.t) :=
  match export_double_uniform_model source with
  | None => pure None
  | Some before => match phase before with
    | Err _ => pure None
    | Okk (middle_scop,after_scop,witnesses) =>
      match import_double_uniform_schedule source middle_scop with
      | Err _ => pure None
      | Okk middle =>
        BIND affine_ok <- DoubleAssignmentValidator.validate source middle -;
        if affine_ok then
          match DoubleAssignmentTilingValidator.import_canonical_tiled_after_poly middle after_scop witnesses with
          | Err _ => pure None
          | Okk tiled =>
            BIND tiling_ok <- DoubleAssignmentTilingValidator.checked_tiling_validate_poly middle tiled witnesses -;
            if tiling_ok then
              BIND generated <- DoubleAssignmentPrepare.prepared_codegen
                (DoubleAssignmentIRs.PolyLang.current_view_pprog tiled) -;
              pure (Some (generated,witnesses))
            else pure None
          end
        else pure None
      end
    end
  end.
Theorem checked_double_tiled_prepared_phase_correct phase source generated witnesses initial final :
  mayReturn (checked_double_tiled_prepared_phase phase source) (Some (generated,witnesses)) ->
  DoubleAssignmentIRs.Loop.semantics generated initial final ->
  DoubleAssignmentIRs.PolyLang.instance_list_semantics source initial final.
Proof.
  unfold checked_double_tiled_prepared_phase.
  destruct (export_double_uniform_model source) as [before|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (phase before) as [[[middle_scop after_scop] ws]|message];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (import_double_uniform_schedule source middle_scop) as [middle|message];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN affine_ok AFFINE.
  destruct affine_ok; [|apply mayReturn_pure in RUN; discriminate].
  destruct (DoubleAssignmentTilingValidator.import_canonical_tiled_after_poly middle after_scop ws) as [tiled|message];
    [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN tiling_ok TILING.
  destruct tiling_ok; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN code CODE.
  apply mayReturn_pure in RUN; inversion RUN; subst code ws.
  intro EXEC.
  pose proof (DoubleAssignmentTilingValidator.checked_tiling_validate_poly_implies_wf_after _ _ _ TILING) as WF.
  pose proof (DoubleAssignmentPrepare.prepared_codegen_correct_general _ _ _ _ CODE WF EXEC) as TILED.
  destruct (DoubleAssignmentTilingValidator.checked_tiling_validate_poly_correct _ _ _ _ _ TILING TILED)
    as [middle_final [MIDDLE SAME]].
  apply double_tiling_state_eq_exact in SAME; subst middle_final.
  destruct (DoubleAssignmentValidator.validate_correct _ _ _ _ true AFFINE eq_refl MIDDLE)
    as [source_final [SOURCE SAME]].
  apply double_tiling_state_eq_exact in SAME; subst source_final; exact SOURCE.
Qed.

Definition checked_double_tiled_prepared_loop phase (source : DoubleAssignmentIRs.Loop.t) :=
  match DoubleAssignmentExtractor.extractor source with
  | Err _ => pure None
  | Okk model => checked_double_tiled_prepared_phase phase model
  end.
Definition checked_double_tiled_prepared_loop_progress phase
  (adapt : Z -> DoubleAssignmentIRs.Loop.t -> result DoubleAssignmentIRs.Loop.t)
  limit (source : DoubleAssignmentIRs.Loop.t) :=
  BIND proposed <- checked_double_tiled_prepared_loop phase source -;
  match proposed with
  | None => pure None
  | Some (raw,witnesses) => match adapt limit raw with
    | Err _ => pure None
    | Okk candidate =>
      let '(_,context,vars) := source in
      BIND valid <- checked_double_extracted_tiling_loops source
        (fst (fst candidate),context,vars) witnesses -;
      if valid then pure (Some candidate) else pure None
    end
  end.
Theorem checked_double_tiled_prepared_loop_progress_at phase adapt limit source generated parameters initial final :
  mayReturn (checked_double_tiled_prepared_loop_progress phase adapt limit source) (Some generated) ->
  length (snd (fst source))=length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst source)) parameters initial final ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) parameters initial final.
Proof.
  destruct source as [[body context] vars].
  intros RUN LENGTH NONALIAS SOURCE; unfold checked_double_tiled_prepared_loop_progress in RUN.
  bind_imp_destruct RUN proposed PROPOSED.
  destruct proposed as [[raw witnesses]|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (adapt limit raw) as [candidate|message]; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN valid VALID; destruct valid; [|apply mayReturn_pure in RUN; discriminate].
  apply mayReturn_pure in RUN; inversion RUN; subst candidate.
  pose proof (@validated_double_extracted_tiling_loops_at body (fst (fst generated)) context vars witnesses
    (rev parameters) initial final ltac:(rewrite length_rev; symmetry; exact LENGTH) NONALIAS VALID) as FORWARD.
  rewrite rev_involutive in FORWARD; apply FORWARD; exact SOURCE.
Qed.

Print Assumptions checked_double_tiled_prepared_phase_correct.
Print Assumptions checked_double_tiled_prepared_loop_progress_at.
