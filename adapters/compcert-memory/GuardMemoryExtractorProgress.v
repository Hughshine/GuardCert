From Stdlib Require Import List ZArith Lia Sorting.Sorted Sorting.Permutation.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.src Require Import ExtractorCorrect.
From polcert.polygen Require Import Result.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops
  GuardMemoryIndexedTrace GuardMemoryExtractorTrace GuardMemoryExtractorCoverage GuardMemoryTraceUniqueness
  GuardMemoryExtractorOrder GuardMemorySequencePolyhedral GuardMemorySequenceOrder GuardMemoryDomainNormalization.
Import ListNotations.
Set Implicit Arguments.
Module MemoryExtractorCorrect := ExtractorCorrect GuardMemoryIRs.

Theorem memory_extracted_stmt_forward st instructions context vars env before after :
  MemoryExtractor.extract_stmt st [] (length env) O [] = Okk instructions ->
  length context = length env ->
  L.loop_semantics st env before after ->
  PL.poly_instance_list_semantics (rev env) (instructions,context,vars) before after.
Proof.
  intros EXTRACT LENGTH RUN.
  set (points := map (memory_extracted_event_point instructions) (indexed_memory_loop_trace O st env)).
  assert (ORDER : StronglySorted memory_sequence_sched_lt points)
    by (unfold points; apply memory_extracted_trace_points_sorted; exact EXTRACT).
  destruct (memory_sequence_strict_order_properties ORDER) as [UNIQUE [SORTED _]].
  destruct (@memory_sequence_ordered_flatten (rev env) instructions points
    ltac:(intro point; unfold points; apply memory_extracted_trace_coverage_iff; exact EXTRACT) UNIQUE)
    as [flattened [FLAT PERM]].
  eapply PL.PolyPointListSema with (ipl := flattened) (sorted_ipl := points).
  - reflexivity.
  - exact FLAT.
  - exact PERM.
  - exact SORTED.
  - apply (proj1 (@memory_extracted_trace_execution st instructions env before after EXTRACT)); exact RUN.
Qed.

Theorem memory_extractor_forward_at st context vars instructions parameters before after :
  MemoryExtractor.extractor (st,context,vars) = Okk (instructions,context,vars) ->
  length parameters = length context ->
  L.loop_semantics st (rev parameters) before after ->
  PL.poly_instance_list_semantics parameters (instructions,context,vars) before after.
Proof.
  intros EXTRACT LENGTH RUN.
  apply MemoryExtractor.extractor_success_inv in EXTRACT as [pis [EXTRACT [_ PROGRAM]]].
  inversion PROGRAM; subst pis; clear PROGRAM.
  assert (EXTRACT' : MemoryExtractor.extract_stmt st [] (length (rev parameters)) O [] = Okk instructions).
  { rewrite length_rev,LENGTH; exact EXTRACT. }
  pose proof (@memory_extracted_stmt_forward st instructions context vars (rev parameters) before after
    EXTRACT' ltac:(rewrite length_rev; symmetry; exact LENGTH) RUN) as POLY.
  rewrite rev_involutive in POLY; exact POLY.
Qed.

Theorem memory_extractor_backward_at st context vars instructions parameters before after :
  MemoryExtractor.extractor (st,context,vars) = Okk (instructions,context,vars) ->
  length parameters = length context ->
  PL.poly_instance_list_semantics parameters (instructions,context,vars) before after ->
  L.loop_semantics st (rev parameters) before after.
Proof.
  intros EXTRACT LENGTH RUN.
  pose proof (@MemoryExtractor.extractor_success_implies_wf_scop st context vars _ EXTRACT) as SCOPE.
  apply MemoryExtractor.extractor_success_inv in EXTRACT as [pis [EXTRACT [WF PROGRAM]]].
  inversion PROGRAM; subst pis; clear PROGRAM.
  inversion RUN as [params program instructions' context' vars' initial final flattened ordered
    PROGRAM FLAT PERM SORTED EXEC]; subst.
  inversion PROGRAM; subst instructions' context' vars'; clear PROGRAM.
  destruct (@MemoryExtractorCorrect.extract_stmt_to_loop_semantics_core_sched_constrs st [] []
    context vars instructions parameters flattened ordered before after SCOPE EXTRACT eq_refl WF
    FLAT PERM SORTED EXEC LENGTH) as [same [LOOP SAME]].
  unfold GuardMemoryIRs.State.eq,GuardMemoryInstr.State.eq in SAME; subst same; exact LOOP.
Qed.

Theorem memory_extractor_execution_at st context vars instructions parameters before after :
  MemoryExtractor.extractor (st,context,vars) = Okk (instructions,context,vars) ->
  length parameters = length context ->
  (L.loop_semantics st (rev parameters) before after <->
   PL.poly_instance_list_semantics parameters (instructions,context,vars) before after).
Proof.
  intros EXTRACT LENGTH; split; intro RUN;
    eapply memory_extractor_forward_at || eapply memory_extractor_backward_at; eassumption.
Qed.

Definition memory_normalize_poly_program (program : PL.t) :=
  let '(instructions,context,vars) := program in (memory_normalized_instructions instructions,context,vars).
Definition checked_memory_loop_equivalence source candidate :=
  match MemoryExtractor.extractor source,MemoryExtractor.extractor candidate with
  | Okk before,Okk after => validate_memory_equivalence
      (memory_normalize_poly_program before) (memory_normalize_poly_program after)
  | _,_ => CoreAlarmed.Base.pure false end.

Theorem validated_memory_affine_loops_at source candidate context vars parameters before after :
  length parameters = length context ->
  GuardMemoryInstr.NonAlias before ->
  mayReturn (checked_memory_loop_equivalence (source,context,vars) (candidate,context,vars)) true ->
  (L.loop_semantics source (rev parameters) before after <->
   L.loop_semantics candidate (rev parameters) before after).
Proof.
  intros LENGTH NONALIAS CHECK; unfold checked_memory_loop_equivalence in CHECK.
  destruct (MemoryExtractor.extractor (source,context,vars)) as [source_program|error] eqn:SOURCE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (MemoryExtractor.extractor (candidate,context,vars)) as [candidate_program|error] eqn:CANDIDATE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (@MemoryExtractor.extractor_success_inv source context vars _ SOURCE) as [source_instructions [_ [_ SOURCE_PROGRAM]]].
  destruct (@MemoryExtractor.extractor_success_inv candidate context vars _ CANDIDATE) as [candidate_instructions [_ [_ CANDIDATE_PROGRAM]]].
  subst source_program candidate_program.
  cbn [memory_normalize_poly_program] in CHECK.
  rewrite (@memory_extractor_execution_at source context vars source_instructions parameters before after SOURCE LENGTH).
  rewrite (@memory_extractor_execution_at candidate context vars candidate_instructions parameters before after CANDIDATE LENGTH).
  rewrite (@memory_domain_normalization_execution parameters source_instructions context vars before after).
  rewrite (@memory_domain_normalization_execution parameters candidate_instructions context vars before after).
  exact (@validated_memory_equivalence_at (memory_normalized_instructions source_instructions,context,vars)
    (memory_normalized_instructions candidate_instructions,context,vars)
    parameters before after (eq_sym LENGTH) (eq_sym LENGTH) NONALIAS CHECK).
Qed.
Print Assumptions memory_extractor_forward_at.
Print Assumptions memory_extractor_execution_at.
Print Assumptions validated_memory_affine_loops_at.
