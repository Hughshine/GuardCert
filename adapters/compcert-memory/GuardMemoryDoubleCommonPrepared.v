From Stdlib Require Import List Bool ZArith String.
From polcert.src Require Import Base OpenScop TilingWitness.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig Misc.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleUniformPrepared GuardMemoryDoubleExtractedTiling GuardMemoryDoubleTiledPrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Export every original schedule in one common coordinate system. The
    exporter is proposal construction: source PolyLang semantics, imported
    source instructions and actual validators remain authoritative. *)
Definition export_double_common_statement (pi : DP.PolyInstr) parameters dimension : option Statement :=
  match export_double_uniform_statement pi parameters dimension with
  | None => None
  | Some statement =>
    let params := List.length parameters in
    let iters := statement.(domain).(meta).(out_dim_nb) in
    let rows := DP.pad_schedule_to_len (params+iters) dimension pi.(DP.pi_schedule) in
    Some {| domain := statement.(domain);
      scattering := {| rel_type := ScttTy; meta := {| row_nb := List.length rows;
        col_nb := List.length rows+iters+params+2; out_dim_nb := List.length rows;
        in_dim_nb := iters; local_dim_nb := 0; param_nb := params |};
        constrs := DP.affine_rows_to_sctt_constrs rows params iters (List.length rows) |};
      access := statement.(access); stmt_exts_opt := statement.(stmt_exts_opt) |}
  end.
Definition export_double_common_model (source : DP.t) : option OpenScop :=
  let '(instructions,parameters,variables) := source in
  let dimension := list_max (map (fun pi => List.length pi.(DP.pi_schedule)) instructions) in
  match export_double_uniform_model source,
    unwrap_option (map (fun pi => export_double_common_statement pi parameters dimension) instructions) with
  | Some before, Some statements => Some {| context := before.(context);
      statements := statements; glb_exts := before.(glb_exts) |}
  | _, _ => None end.

Lemma export_double_common_statement_payload pi parameters dimension proposed :
  export_double_common_statement pi parameters dimension=Some proposed ->
  exists original, export_double_uniform_statement pi parameters dimension=Some original /\
    proposed.(domain)=original.(domain) /\ proposed.(access)=original.(access) /\
    proposed.(stmt_exts_opt)=original.(stmt_exts_opt).
Proof.
  unfold export_double_common_statement.
  destruct (export_double_uniform_statement pi parameters dimension) as [original|] eqn:EXPORTED;
    [|discriminate].
  intro SAME; inversion SAME; subst proposed; exists original; repeat split; reflexivity.
Qed.

Definition checked_double_common_prepared_phase
  (phase : OpenScop -> result (OpenScop * OpenScop * list statement_tiling_witness))
  (source : DoubleAssignmentIRs.PolyLang.t) :=
  match export_double_common_model source with
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
Theorem checked_double_common_prepared_phase_correct phase source generated witnesses initial final :
  mayReturn (checked_double_common_prepared_phase phase source) (Some (generated,witnesses)) ->
  DoubleAssignmentIRs.Loop.semantics generated initial final ->
  DoubleAssignmentIRs.PolyLang.instance_list_semantics source initial final.
Proof.
  unfold checked_double_common_prepared_phase.
  destruct (export_double_common_model source) as [before|];
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

Definition checked_double_common_prepared_loop phase (source : DoubleAssignmentIRs.Loop.t) :=
  match DoubleAssignmentExtractor.extractor source with
  | Err _ => pure None
  | Okk model => checked_double_common_prepared_phase phase model
  end.
Theorem checked_double_common_prepared_loop_correct phase source generated witnesses initial final :
  mayReturn (checked_double_common_prepared_loop phase source) (Some (generated,witnesses)) ->
  DoubleAssignmentIRs.Loop.semantics generated initial final ->
  DoubleAssignmentIRs.Loop.semantics source initial final.
Proof.
  unfold checked_double_common_prepared_loop.
  destruct (DoubleAssignmentExtractor.extractor source) as [model|message] eqn:EXTRACT;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intros RUN EXEC.
  pose proof (@checked_double_common_prepared_phase_correct phase model generated witnesses initial final RUN EXEC) as MODEL.
  destruct (DoubleAssignmentExtractor.extractor_correct _ _ _ _ EXTRACT MODEL) as [result [SOURCE SAME]].
  unfold DoubleAssignmentIRs.State.eq, DoubleAssignmentInstr.State.eq in SAME; subst result; exact SOURCE.
Qed.

Print Assumptions export_double_common_statement_payload.
Print Assumptions checked_double_common_prepared_phase_correct.
Print Assumptions checked_double_common_prepared_loop_correct.
