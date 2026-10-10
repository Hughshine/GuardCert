From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.polygen Require Import Result.
From Vpl Require Import Impure.
From Guard Require Import PolCertTilingExecutionOn.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleCandidateProgress GuardMemoryDoubleExtractedTiling
  GuardMemoryDoubleRetainedPhase GuardMemoryDoublePieceModel GuardMemoryDoublePieceLoops.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Module DoubleTilingExecution := PolCertTilingExecutionOnFor DoubleAssignmentIRs DoubleTiling.

Lemma double_piece_tiling_checker_exact source candidate witnesses :
  DoubleTilingExecution.P.validate_memory_tiling_equivalence source candidate witnesses =
  DoubleTiling.validate_memory_tiling_equivalence source candidate witnesses.
Proof. reflexivity. Qed.

Theorem checked_double_retained_phase_equivalence_at phase instructions context vars generated model witnesses
  parameters initial final :
  mayReturn (checked_double_retained_phase phase (instructions,context,vars))
    (Some (generated,model,witnesses)) ->
  length parameters=length context -> DoubleAssignmentInstr.NonAlias initial ->
  (DoubleAssignmentIRs.PolyLang.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   DoubleAssignmentIRs.PolyLang.poly_instance_list_semantics parameters model initial final).
Proof.
  intros CHECK LENGTH NONALIAS.
  destruct (@checked_double_retained_phase_sound phase (instructions,context,vars) generated model witnesses CHECK)
    as [middle [tiled [MODEL [AFFINE [_ [TILING [SHAPE _]]]]]]].
  subst model; cbn [RP.current_view_pprog].
  rewrite (@double_tiling_current_view_execution parameters tiled context vars initial final LENGTH
    (@double_tiling_current_shape_sound tiled SHAPE)).
  eapply iff_trans.
  - exact (@validated_double_equivalence_at (instructions,context,vars) (middle,context,vars)
      parameters initial final (eq_sym LENGTH) (eq_sym LENGTH) NONALIAS AFFINE).
  - eapply DoubleTilingExecution.validated_tiling_execution_at;
      [exact double_tiling_state_eq_exact|exact LENGTH|exact NONALIAS|].
    exact TILING.
Qed.

Theorem checked_double_piece_actual_loops_equivalence_at phase guards source candidate context vars
  source_instructions candidate_instructions generated model witnesses groups coverage parameters initial final :
  DoubleAssignmentExtractor.extractor (source,context,vars)=Okk (source_instructions,context,vars) ->
  DoubleAssignmentExtractor.extractor (candidate,context,vars)=Okk (candidate_instructions,context,vars) ->
  mayReturn (checked_double_retained_phase phase (source_instructions,context,vars))
    (Some (generated,model,witnesses)) ->
  mayReturn (check_double_piece_model guards model (candidate_instructions,context,vars) groups coverage) true ->
  length parameters=length context ->
  Forall (fun row=>(length (fst row)<=length parameters)%nat) guards ->
  in_poly parameters guards=true -> DoubleAssignmentInstr.NonAlias initial ->
  (DoubleAssignmentIRs.Loop.loop_semantics source (rev parameters) initial final <->
   DoubleAssignmentIRs.Loop.loop_semantics candidate (rev parameters) initial final).
Proof.
  intros SOURCE_EXTRACT CANDIDATE_EXTRACT PHASE CHECK LENGTH WIDTH ACCEPT NONALIAS.
  assert (MODEL_LENGTH : length (snd (fst model))=length parameters).
  { destruct (@checked_double_retained_phase_sound phase (source_instructions,context,vars)
      generated model witnesses PHASE) as [middle [tiled [MODEL _]]].
    rewrite MODEL; cbn; symmetry; exact LENGTH. }
  eapply iff_trans.
  - exact (@double_tiling_extractor_execution_at source context vars source_instructions
      parameters initial final SOURCE_EXTRACT LENGTH).
  - eapply iff_trans.
    + exact (@checked_double_retained_phase_equivalence_at phase source_instructions context vars
        generated model witnesses parameters initial final PHASE LENGTH NONALIAS).
    + exact (@checked_double_piece_model_to_actual_loop_at guards model candidate context vars
        candidate_instructions groups coverage parameters initial final CANDIDATE_EXTRACT LENGTH
        MODEL_LENGTH WIDTH ACCEPT NONALIAS CHECK).
Qed.
Print Assumptions double_piece_tiling_checker_exact.
Print Assumptions DoubleTilingExecution.tiling_complete_isomorphism.
Print Assumptions DoubleTilingExecution.validated_tiling_execution_at.
Print Assumptions checked_double_retained_phase_equivalence_at.
Print Assumptions checked_double_piece_actual_loops_equivalence_at.
