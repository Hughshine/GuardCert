From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PointWitness.
From polcert.polygen Require Import Result.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops
  GuardMemoryExtractorTrace GuardMemoryExtractorProgress GuardMemoryDomainNormalization GuardMemoryCoordinateSwap
  GuardMemoryReindexedExtractor GuardMemoryDomainAlignment.
Import ListNotations.
Set Implicit Arguments.

Definition check_memory_poly_domain_candidates source target :=
  let '(source_instructions,context,vars) := source in
  let '(target_instructions,target_context,target_vars) := target in
  BIND aligned <- memory_align_domains source_instructions target_instructions -;
  match aligned with
  | Some instructions => validate_memory_equivalence (source_instructions,context,vars) (instructions,target_context,target_vars)
  | None => CoreAlarmed.Base.pure false end.
Definition checked_memory_equivalent_domain_loops source candidate swaps :=
  match MemoryExtractor.extractor source,MemoryExtractor.extractor candidate with
  | Okk before,Okk after => check_memory_poly_domain_candidates
      (memory_normalize_poly_program before) (memory_reindex_poly_program swaps after)
  | _,_ => CoreAlarmed.Base.pure false end.
Theorem validated_memory_equivalent_domain_loops_at source candidate context vars swaps parameters before after :
  length parameters = length context -> GuardMemoryInstr.NonAlias before ->
  mayReturn (checked_memory_equivalent_domain_loops (source,context,vars) (candidate,context,vars) swaps) true ->
  (L.loop_semantics source (rev parameters) before after <->
   L.loop_semantics candidate (rev parameters) before after).
Proof.
  intros LENGTH NONALIAS CHECK; unfold checked_memory_equivalent_domain_loops in CHECK.
  destruct (MemoryExtractor.extractor (source,context,vars)) as [source_program|error] eqn:SOURCE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (MemoryExtractor.extractor (candidate,context,vars)) as [candidate_program|error] eqn:CANDIDATE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (@MemoryExtractor.extractor_success_inv source context vars _ SOURCE) as [source_instructions [_ [_ SOURCE_PROGRAM]]].
  destruct (@MemoryExtractor.extractor_success_inv candidate context vars _ CANDIDATE) as [candidate_instructions [_ [_ CANDIDATE_PROGRAM]]].
  subst source_program candidate_program.
  cbn [memory_normalize_poly_program memory_reindex_poly_program check_memory_poly_domain_candidates] in CHECK.
  bind_imp_destruct CHECK aligned_result ALIGN.
  destruct aligned_result as [aligned|]; [|apply mayReturn_pure in CHECK; discriminate].
  rewrite (@memory_extractor_execution_at source context vars source_instructions parameters before after SOURCE LENGTH).
  rewrite (@memory_extractor_execution_at candidate context vars candidate_instructions parameters before after CANDIDATE LENGTH).
  rewrite (@memory_domain_normalization_execution parameters source_instructions context vars before after).
  rewrite (@memory_reindexed_execution (length context) swaps parameters candidate_instructions context vars before after
    LENGTH (@memory_extracted_identity_representation candidate context vars candidate_instructions CANDIDATE)).
  rewrite (@memory_domain_normalization_execution parameters
    (memory_reindexed_instructions (length context) swaps candidate_instructions) context vars before after).
  rewrite (@memory_aligned_domains_execution parameters (memory_normalized_instructions source_instructions)
    (memory_normalized_instructions (memory_reindexed_instructions (length context) swaps candidate_instructions))
    aligned context vars before after ALIGN).
  exact (@validated_memory_equivalence_at (memory_normalized_instructions source_instructions,context,vars)
    (aligned,context,vars)
    parameters before after (eq_sym LENGTH) (eq_sym LENGTH) NONALIAS CHECK).
Qed.
Print Assumptions validated_memory_equivalent_domain_loops_at.
