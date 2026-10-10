From Stdlib Require Import List Bool ZArith.
From polcert.src Require Import OpenScop TilingWitness.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleUniformPrepared GuardMemoryDoubleExtractedTiling GuardMemoryDoubleCommonPrepared
  GuardMemoryEqualityReducedPrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Module RP := DoubleAssignmentIRs.PolyLang.

(** Keep the actual checked tiled model for the final piece bridge. Both
    transformation directions are checked; raw codegen is not a forward proof. *)
Definition checked_double_retained_phase
  (phase : OpenScop -> result (OpenScop * OpenScop * list statement_tiling_witness))
  (source : RP.t) :=
  let '(_,context,vars) := source in
  match export_double_common_model source with
  | None=>pure None
  | Some before=>match phase before with
    | Err _=>pure None
    | Okk (middle_scop,after_scop,witnesses)=>
      match import_double_uniform_schedule source middle_scop with
      | Err _=>pure None
      | Okk imported_middle=>
        let middle := (fst (fst imported_middle),context,vars) in
        BIND affine_ok <- validate_double_equivalence source middle -;
        if affine_ok then
          match DoubleAssignmentTilingValidator.import_canonical_tiled_after_poly middle after_scop witnesses with
          | Err _=>pure None
          | Okk imported_tiled=>
            let tiled := (fst (fst imported_tiled),context,vars) in
            BIND tiling_ok <- DoubleAssignmentTilingValidator.checked_tiling_validate_poly middle tiled witnesses -;
            if tiling_ok then
              BIND forward_ok <- DoubleTiling.validate_memory_tiling_equivalence middle tiled witnesses -;
              if forward_ok && double_tiling_current_shape (fst (fst tiled)) then
                let model := RP.current_view_pprog tiled in
                BIND generated <- DoubleEqualityReducedPrepare.prepared_codegen model -;
                pure (Some (generated,model,witnesses))
              else pure None
            else pure None
          end
        else pure None
      end
    end
  end.

Definition double_retained_phase_certificate source generated model witnesses :=
  let '(instructions,context,vars) := source in
  exists middle tiled,
    model=RP.current_view_pprog (tiled,context,vars) /\
    mayReturn (validate_double_equivalence (instructions,context,vars) (middle,context,vars)) true /\
    mayReturn (DoubleAssignmentTilingValidator.checked_tiling_validate_poly
      (middle,context,vars) (tiled,context,vars) witnesses) true /\
    mayReturn (DoubleTiling.validate_memory_tiling_equivalence
      (middle,context,vars) (tiled,context,vars) witnesses) true /\
    double_tiling_current_shape tiled=true /\
    mayReturn (DoubleEqualityReducedPrepare.prepared_codegen model) generated.
Theorem checked_double_retained_phase_sound phase source generated model witnesses :
  mayReturn (checked_double_retained_phase phase source) (Some (generated,model,witnesses)) ->
  double_retained_phase_certificate source generated model witnesses.
Proof.
  destruct source as [[instructions context] vars].
  unfold checked_double_retained_phase,double_retained_phase_certificate.
  destruct (export_double_common_model (instructions,context,vars)) as [before|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (phase before) as [[[middle_scop after_scop] ws]|message];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (import_double_uniform_schedule (instructions,context,vars) middle_scop) as [[[middle imported_context] imported_vars]|message];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; cbn [fst snd] in CHECK; bind_imp_destruct CHECK affine_ok AFFINE; destruct affine_ok;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (DoubleAssignmentTilingValidator.import_canonical_tiled_after_poly (middle,context,vars) after_scop ws)
    as [[[tiled tiled_context] tiled_vars]|message];
    [|apply mayReturn_pure in CHECK; discriminate].
  cbn [fst snd] in CHECK; bind_imp_destruct CHECK tiling_ok TILING; destruct tiling_ok;
    [|apply mayReturn_pure in CHECK; discriminate].
  bind_imp_destruct CHECK forward_ok FORWARD.
  destruct (forward_ok && double_tiling_current_shape tiled) eqn:SHAPE;
    [|apply mayReturn_pure in CHECK; discriminate].
  apply andb_true_iff in SHAPE as [OK SHAPE]; subst forward_ok.
  bind_imp_destruct CHECK code CODE.
  apply mayReturn_pure in CHECK; inversion CHECK; subst code model ws.
  exists middle,tiled; repeat split; auto.
Qed.
Theorem checked_double_retained_phase_forward_at phase instructions context vars generated model witnesses parameters initial final :
  mayReturn (checked_double_retained_phase phase (instructions,context,vars)) (Some (generated,model,witnesses)) ->
  length parameters=length context -> DoubleAssignmentInstr.NonAlias initial ->
  RP.poly_instance_list_semantics parameters (instructions,context,vars) initial final ->
  RP.poly_instance_list_semantics parameters model initial final.
Proof.
  intros CHECK LENGTH NONALIAS SOURCE.
  destruct (@checked_double_retained_phase_sound phase (instructions,context,vars) generated model witnesses CHECK)
    as [middle [tiled [MODEL [AFFINE [TILING [FORWARD [SHAPE CODE]]]]]]].
  subst model; cbn [RP.current_view_pprog].
  apply (proj2 (@double_tiling_current_view_execution parameters tiled context vars initial final LENGTH
    (@double_tiling_current_shape_sound tiled SHAPE))).
  eapply (DoubleTiling.validated_memory_multiple_tiling_progress_at double_tiling_state_eq_exact);
    [exact LENGTH|exact NONALIAS|exact FORWARD|].
  apply (proj1 (@validated_double_equivalence_at (instructions,context,vars) (middle,context,vars)
    parameters initial final (eq_sym LENGTH) (eq_sym LENGTH) NONALIAS AFFINE)); exact SOURCE.
Qed.
Theorem checked_double_retained_phase_raw_backward phase source generated model witnesses initial final :
  mayReturn (checked_double_retained_phase phase source) (Some (generated,model,witnesses)) ->
  DoubleAssignmentIRs.Loop.semantics generated initial final -> RP.instance_list_semantics source initial final.
Proof.
  destruct source as [[instructions context] vars]; intros CHECK EXEC.
  destruct (@checked_double_retained_phase_sound phase (instructions,context,vars) generated model witnesses CHECK)
    as [middle [tiled [MODEL [AFFINE [TILING [FORWARD [SHAPE CODE]]]]]]].
  subst model.
  pose proof (DoubleAssignmentTilingValidator.checked_tiling_validate_poly_implies_wf_after _ _ _ TILING) as WF.
  pose proof (DoubleEqualityReducedPrepare.prepared_codegen_correct_general _ _ _ _ CODE WF EXEC) as TILED.
  destruct (DoubleAssignmentTilingValidator.checked_tiling_validate_poly_correct _ _ _ _ _ TILING TILED)
    as [middle_final [MIDDLE SAME]].
  apply double_tiling_state_eq_exact in SAME; subst middle_final.
  destruct (validate_double_equivalence_results AFFINE) as [BACKWARD _].
  destruct (DoubleAssignmentValidator.validate_correct _ _ _ _ true BACKWARD eq_refl MIDDLE)
    as [source_final [SOURCE SAME]].
  apply double_tiling_state_eq_exact in SAME; subst source_final; exact SOURCE.
Qed.

Print Assumptions checked_double_retained_phase_sound.
Print Assumptions checked_double_retained_phase_forward_at.
Print Assumptions checked_double_retained_phase_raw_backward.
