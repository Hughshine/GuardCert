From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.polygen Require Import Result.
From Vpl Require Import Impure.
From Guard Require Import PolCertCandidateRepresentation.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoublePrepared GuardMemoryDoublePreparedAt.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Module DoubleCandidate := PolCertCandidateRepresentationFor DoubleAssignmentIRs.
Module CandidateLoop := DoubleAssignmentIRs.Loop.
Module CandidatePoly := DoubleAssignmentIRs.PolyLang.

Lemma double_extractor_execution_at body context vars instructions parameters initial final :
  DoubleAssignmentExtractor.extractor (body,context,vars) = Okk (instructions,context,vars) ->
  length context = length parameters ->
  (CandidateLoop.loop_semantics body parameters initial final <->
   CandidatePoly.poly_instance_list_semantics (rev parameters) (instructions,context,vars) initial final).
Proof.
  intros EXTRACT LENGTH; split; intro RUN.
  - pose proof (@DoubleCandidate.memory_extracted_stmt_forward body instructions context vars parameters initial final).
    apply DoubleAssignmentExtractor.extractor_success_inv in EXTRACT as [pis [EXTRACT [_ PROGRAM]]].
    inversion PROGRAM; subst pis; clear PROGRAM.
    rewrite LENGTH in EXTRACT; eauto.
  - destruct (@DoubleAssignmentParameters.extractor_correct_at
      (body,context,vars) (instructions,context,vars) parameters initial final EXTRACT LENGTH RUN)
      as [result [SOURCE SAME]].
    unfold DoubleAssignmentIRs.State.eq,DoubleAssignmentInstr.State.eq in SAME.
    subst result; exact SOURCE.
Qed.

Definition check_double_poly_domain_candidates source target :=
  let '(source_instructions,context,vars) := source in
  let '(target_instructions,target_context,target_vars) := target in
  BIND aligned <- DoubleCandidate.memory_align_domains source_instructions target_instructions -;
  match aligned with
  | Some instructions => validate_double_equivalence (source_instructions,context,vars) (instructions,target_context,target_vars)
  | None => pure false end.
Definition checked_double_candidate_loops source candidate swaps :=
  match DoubleAssignmentExtractor.extractor source,DoubleAssignmentExtractor.extractor candidate with
  | Okk before,Okk after => check_double_poly_domain_candidates
      (DoubleCandidate.memory_normalize_poly_program before) (DoubleCandidate.memory_reindex_poly_program swaps after)
  | _,_ => pure false end.

Theorem validated_double_candidate_loops_at source candidate context vars swaps parameters initial final :
  length context = length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  mayReturn (checked_double_candidate_loops (source,context,vars) (candidate,context,vars) swaps) true ->
  (CandidateLoop.loop_semantics source parameters initial final <->
   CandidateLoop.loop_semantics candidate parameters initial final).
Proof.
  intros LENGTH NONALIAS CHECK; unfold checked_double_candidate_loops in CHECK.
  destruct (DoubleAssignmentExtractor.extractor (source,context,vars)) as [source_program|error] eqn:SOURCE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (DoubleAssignmentExtractor.extractor (candidate,context,vars)) as [candidate_program|error] eqn:CANDIDATE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (@DoubleAssignmentExtractor.extractor_success_inv source context vars _ SOURCE)
    as [source_instructions [_ [_ SOURCE_PROGRAM]]].
  destruct (@DoubleAssignmentExtractor.extractor_success_inv candidate context vars _ CANDIDATE)
    as [candidate_instructions [_ [_ CANDIDATE_PROGRAM]]].
  subst source_program candidate_program.
  cbn [DoubleCandidate.memory_normalize_poly_program DoubleCandidate.memory_reindex_poly_program
    check_double_poly_domain_candidates] in CHECK.
  bind_imp_destruct CHECK aligned_result ALIGN.
  destruct aligned_result as [aligned|]; [|apply mayReturn_pure in CHECK; discriminate].
  rewrite (@double_extractor_execution_at source context vars source_instructions parameters initial final SOURCE LENGTH).
  rewrite (@double_extractor_execution_at candidate context vars candidate_instructions parameters initial final CANDIDATE LENGTH).
  rewrite (@DoubleCandidate.memory_domain_normalization_execution (rev parameters)
    source_instructions context vars initial final).
  rewrite (@DoubleCandidate.memory_reindexed_execution (length context) swaps (rev parameters)
    candidate_instructions context vars initial final
    ltac:(rewrite length_rev; exact LENGTH)
    ltac:(rewrite length_rev; symmetry; exact LENGTH)
    (@DoubleCandidate.memory_extracted_identity_representation candidate context vars candidate_instructions CANDIDATE)).
  rewrite (@DoubleCandidate.memory_domain_normalization_execution (rev parameters)
    (DoubleCandidate.memory_reindexed_instructions (length context) swaps candidate_instructions) context vars initial final).
  rewrite (@DoubleCandidate.memory_aligned_domains_execution (rev parameters)
    (DoubleCandidate.memory_normalized_instructions source_instructions)
    (DoubleCandidate.memory_normalized_instructions
      (DoubleCandidate.memory_reindexed_instructions (length context) swaps candidate_instructions))
    aligned context vars initial final ltac:(rewrite length_rev; exact LENGTH) ALIGN).
  exact (@validated_double_equivalence_at
    (DoubleCandidate.memory_normalized_instructions source_instructions,context,vars) (aligned,context,vars)
    (rev parameters) initial final ltac:(cbn; rewrite length_rev; exact LENGTH)
    ltac:(cbn; rewrite length_rev; exact LENGTH) NONALIAS CHECK).
Qed.

(** Validate the actual final generated body under the source's named context.
    The producer supplies only an adjacent-coordinate swap witness. A failed
    final extraction, domain check, or dependence check refuses the candidate. *)
Definition checked_double_prepared_loop_progress schedule swaps (source : CandidateLoop.t) :=
  BIND generated <- checked_double_prepared_loop schedule source -;
  match generated with
  | None => pure None
  | Some candidate =>
    let '(body,context,vars) := source in
    BIND valid <- checked_double_candidate_loops source (fst (fst candidate),context,vars) swaps -;
    if valid then pure (Some candidate) else pure None
  end.

Theorem checked_double_prepared_loop_progress_at schedule swaps source generated parameters initial final :
  mayReturn (checked_double_prepared_loop_progress schedule swaps source) (Some generated) ->
  length (snd (fst source)) = length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  (CandidateLoop.loop_semantics (fst (fst source)) parameters initial final <->
   CandidateLoop.loop_semantics (fst (fst generated)) parameters initial final).
Proof.
  destruct source as [[body context] vars].
  intros RUN LENGTH NONALIAS; unfold checked_double_prepared_loop_progress in RUN.
  bind_imp_destruct RUN generated_result GENERATED.
  destruct generated_result as [candidate|]; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN valid VALID; destruct valid;
    [|apply mayReturn_pure in RUN; discriminate].
  apply mayReturn_pure in RUN; inversion RUN; subst candidate.
  exact (@validated_double_candidate_loops_at body (fst (fst generated)) context vars swaps
    parameters initial final LENGTH NONALIAS VALID).
Qed.

Print Assumptions DoubleCandidate.memory_extracted_stmt_forward.
Print Assumptions DoubleCandidate.memory_extractor_forward_at.
Print Assumptions DoubleCandidate.memory_point_isomorphism_execution.
Print Assumptions DoubleCandidate.memory_coordinate_swap_execution.
Print Assumptions DoubleCandidate.memory_reindexed_execution.
Print Assumptions DoubleCandidate.memory_check_domain_equivalence_correct.
Print Assumptions DoubleCandidate.memory_aligned_domains_execution.
Print Assumptions double_extractor_execution_at.
Print Assumptions validated_double_candidate_loops_at.
Print Assumptions checked_double_prepared_loop_progress_at.
