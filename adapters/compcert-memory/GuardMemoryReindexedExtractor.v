From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PointWitness.
From polcert.polygen Require Import Result.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops
  GuardMemoryExtractorTrace GuardMemoryExtractorProgress GuardMemoryDomainNormalization GuardMemoryCoordinateSwap.
Import ListNotations.
Set Implicit Arguments.

Lemma memory_exact_columns_forall dimension rows : exact_listzzs_cols dimension rows ->
  Forall (fun row => length (fst row) = dimension) rows.
Proof. intros WIDTH; apply Forall_forall; intros [coefficients bias] MEMBER;
  exact (WIDTH coefficients bias (coefficients,bias) MEMBER eq_refl). Qed.
Lemma memory_extracted_identity_representation st context vars instructions :
  MemoryExtractor.extractor (st,context,vars) = Okk (instructions,context,vars) ->
  Forall (memory_identity_representation (length context)) instructions.
Proof.
  intro EXTRACT; apply MemoryExtractor.extractor_success_inv in EXTRACT as [pis [_ [WF PROGRAM]]].
  inversion PROGRAM; subst pis.
  apply MemoryExtractor.check_extracted_wf_spec in WF as [_ ALL].
  apply Forall_forall; intros pi MEMBER.
  pose proof (@MemoryExtractor.Val.check_wf_polyinstr_affine_correct pi context vars
    (proj1 (forallb_forall _ _) ALL pi MEMBER)) as [WF [IDENTITY _]].
  unfold PL.wf_pinstr in WF; cbn zeta in WF.
  destruct WF as [_ [_ [_ [_ [DOMAIN [TRANSFORM [_ [SCHEDULE _]]]]]]]].
  unfold memory_identity_representation; split; [exact IDENTITY|].
  split; [apply memory_exact_columns_forall; exact DOMAIN|].
  split; [apply memory_exact_columns_forall; exact SCHEDULE|].
  apply memory_exact_columns_forall; rewrite IDENTITY in TRANSFORM; exact TRANSFORM.
Qed.
Fixpoint memory_reindexed_instructions dimension swaps instructions :=
  match swaps with
  | [] => instructions
  | position::rest => memory_reindexed_instructions dimension rest
      (memory_swap_instructions (dimension+position)%nat instructions)
  end.
Lemma memory_reindexed_identity_representation dimension swaps instructions :
  Forall (memory_identity_representation dimension) instructions ->
  Forall (memory_identity_representation dimension) (memory_reindexed_instructions dimension swaps instructions).
Proof.
  revert instructions; induction swaps; intros instructions REPRESENTATIONS; cbn; [exact REPRESENTATIONS|].
  apply IHswaps; unfold memory_swap_instructions; apply Forall_map; eapply Forall_impl; [|exact REPRESENTATIONS].
  intros pi REP; apply memory_swap_instruction_representation; exact REP.
Qed.
Theorem memory_reindexed_execution dimension swaps parameters instructions context vars initial final :
  length parameters = dimension -> Forall (memory_identity_representation dimension) instructions ->
  (PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (memory_reindexed_instructions dimension swaps instructions,context,vars) initial final).
Proof.
  revert instructions; induction swaps; intros instructions LENGTH REPRESENTATIONS; cbn; [reflexivity|].
  rewrite (@memory_coordinate_swap_execution (dimension+a)%nat parameters instructions context vars initial final
    ltac:(lia) ltac:(rewrite LENGTH; exact REPRESENTATIONS)).
  apply IHswaps; [exact LENGTH|].
  unfold memory_swap_instructions; apply Forall_map; eapply Forall_impl; [|exact REPRESENTATIONS].
  intros pi REP; apply memory_swap_instruction_representation; exact REP.
Qed.
Definition memory_reindex_poly_program swaps (program : PL.t) :=
  let '(instructions,context,vars) := program in
  (memory_normalized_instructions (memory_reindexed_instructions (length context) swaps instructions),context,vars).
Definition checked_memory_reindexed_loop_equivalence source candidate swaps :=
  match MemoryExtractor.extractor source,MemoryExtractor.extractor candidate with
  | Okk before,Okk after => validate_memory_equivalence
      (memory_normalize_poly_program before) (memory_reindex_poly_program swaps after)
  | _,_ => CoreAlarmed.Base.pure false end.
Theorem validated_memory_reindexed_loops_at source candidate context vars swaps parameters before after :
  length parameters = length context -> GuardMemoryInstr.NonAlias before ->
  mayReturn (checked_memory_reindexed_loop_equivalence (source,context,vars) (candidate,context,vars) swaps) true ->
  (L.loop_semantics source (rev parameters) before after <->
   L.loop_semantics candidate (rev parameters) before after).
Proof.
  intros LENGTH NONALIAS CHECK; unfold checked_memory_reindexed_loop_equivalence in CHECK.
  destruct (MemoryExtractor.extractor (source,context,vars)) as [source_program|error] eqn:SOURCE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (MemoryExtractor.extractor (candidate,context,vars)) as [candidate_program|error] eqn:CANDIDATE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (@MemoryExtractor.extractor_success_inv source context vars _ SOURCE) as [source_instructions [_ [_ SOURCE_PROGRAM]]].
  destruct (@MemoryExtractor.extractor_success_inv candidate context vars _ CANDIDATE) as [candidate_instructions [_ [_ CANDIDATE_PROGRAM]]].
  subst source_program candidate_program.
  cbn [memory_normalize_poly_program memory_reindex_poly_program] in CHECK.
  rewrite (@memory_extractor_execution_at source context vars source_instructions parameters before after SOURCE LENGTH).
  rewrite (@memory_extractor_execution_at candidate context vars candidate_instructions parameters before after CANDIDATE LENGTH).
  rewrite (@memory_domain_normalization_execution parameters source_instructions context vars before after).
  rewrite (@memory_reindexed_execution (length context) swaps parameters candidate_instructions context vars before after
    LENGTH (@memory_extracted_identity_representation candidate context vars candidate_instructions CANDIDATE)).
  rewrite (@memory_domain_normalization_execution parameters
    (memory_reindexed_instructions (length context) swaps candidate_instructions) context vars before after).
  exact (@validated_memory_equivalence_at (memory_normalized_instructions source_instructions,context,vars)
    (memory_normalized_instructions (memory_reindexed_instructions (length context) swaps candidate_instructions),context,vars)
    parameters before after (eq_sym LENGTH) (eq_sym LENGTH) NONALIAS CHECK).
Qed.
Print Assumptions memory_extracted_identity_representation.
Print Assumptions memory_reindexed_execution.
Print Assumptions validated_memory_reindexed_loops_at.
