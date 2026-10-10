From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.polygen Require Import Result.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleCandidateProgress GuardMemoryDoubleExtractedTiling
  GuardMemoryDoubleRetainedPhase GuardMemoryDoublePieceModel.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** The actual candidate extractor's existing bidirectional execution theorem
    connects the checked model result to finite Loop execution. This does not
    provide independent Clight progress, machine safety or site installation. *)
Theorem checked_double_piece_model_to_actual_loop_at guards source candidate context vars
  instructions groups coverage parameters initial final :
  DoubleAssignmentExtractor.extractor (candidate,context,vars)=Okk (instructions,context,vars) ->
  length parameters=length context ->
  length (snd (fst source))=length parameters ->
  Forall (fun row=>(length (fst row)<=length parameters)%nat) guards ->
  in_poly parameters guards=true -> DoubleAssignmentInstr.NonAlias initial ->
  mayReturn (check_double_piece_model guards source (instructions,context,vars) groups coverage) true ->
  (DoubleAssignmentIRs.PolyLang.poly_instance_list_semantics parameters source initial final <->
   DoubleAssignmentIRs.Loop.loop_semantics candidate (rev parameters) initial final).
Proof.
  intros EXTRACT LENGTH SOURCE_LENGTH WIDTH ACCEPT NONALIAS CHECK.
  eapply iff_trans.
  - exact (@checked_double_piece_model_equivalence_at guards source (instructions,context,vars)
      groups coverage parameters initial final SOURCE_LENGTH WIDTH ACCEPT NONALIAS CHECK).
  - symmetry; exact (@double_tiling_extractor_execution_at candidate context vars instructions
      parameters initial final EXTRACT LENGTH).
Qed.

Theorem checked_double_piece_actual_loops_forward_at phase guards source candidate context vars
  source_instructions candidate_instructions generated model witnesses groups coverage parameters initial final :
  DoubleAssignmentExtractor.extractor (source,context,vars)=Okk (source_instructions,context,vars) ->
  DoubleAssignmentExtractor.extractor (candidate,context,vars)=Okk (candidate_instructions,context,vars) ->
  mayReturn (checked_double_retained_phase phase (source_instructions,context,vars))
    (Some (generated,model,witnesses)) ->
  mayReturn (check_double_piece_model guards model (candidate_instructions,context,vars) groups coverage) true ->
  length parameters=length context ->
  Forall (fun row=>(length (fst row)<=length parameters)%nat) guards ->
  in_poly parameters guards=true -> DoubleAssignmentInstr.NonAlias initial ->
  DoubleAssignmentIRs.Loop.loop_semantics source (rev parameters) initial final ->
  DoubleAssignmentIRs.Loop.loop_semantics candidate (rev parameters) initial final.
Proof.
  intros SOURCE_EXTRACT CANDIDATE_EXTRACT PHASE CHECK LENGTH WIDTH ACCEPT NONALIAS SOURCE.
  assert (MODEL_LENGTH : length (snd (fst model))=length parameters).
  { destruct (@checked_double_retained_phase_sound phase (source_instructions,context,vars)
      generated model witnesses PHASE) as [middle [tiled [MODEL _]]].
    rewrite MODEL; cbn; symmetry; exact LENGTH. }
  apply (proj1 (@checked_double_piece_model_to_actual_loop_at guards model candidate context vars
    candidate_instructions groups coverage parameters initial final CANDIDATE_EXTRACT LENGTH
    MODEL_LENGTH WIDTH ACCEPT NONALIAS CHECK)).
  eapply checked_double_retained_phase_forward_at; [exact PHASE|exact LENGTH|exact NONALIAS|].
  apply (proj1 (@double_tiling_extractor_execution_at source context vars source_instructions
    parameters initial final SOURCE_EXTRACT LENGTH)); exact SOURCE.
Qed.
Print Assumptions checked_double_piece_model_to_actual_loop_at.
Print Assumptions checked_double_piece_actual_loops_forward_at.
