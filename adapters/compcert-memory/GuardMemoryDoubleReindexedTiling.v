From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.polygen Require Import Result.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleCandidateProgress GuardMemoryDoubleExtractedTiling.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Reindexing is representation evidence, not a change to the generated Loop.
    The existing coordinate-isomorphism proof transports its actual execution. *)
Definition checked_double_reindexed_tiling_loops source candidate witnesses swaps :=
  match DoubleAssignmentExtractor.extractor source,DoubleAssignmentExtractor.extractor candidate with
  | Okk (before,context,vars),Okk (after,_,_) =>
    let normalized_before := DoubleCandidate.memory_normalized_instructions before in
    let normalized_after := DoubleCandidate.memory_normalized_instructions
      (DoubleCandidate.memory_reindexed_instructions (length context) swaps after) in
    match double_attach_tiling_instructions (length context) normalized_before normalized_after witnesses with
    | Some tiled =>
      if double_tiling_current_shape tiled then
        BIND aligned <- DoubleCandidate.memory_align_domains (map (PL.current_view_pi (length context)) tiled) normalized_after -;
        match aligned with
        | Some aligned => if double_tiling_pinstr_list_eqb (map (PL.current_view_pi (length context)) tiled) aligned
          then DoubleTiling.validate_memory_tiling_equivalence (normalized_before,context,vars) (tiled,context,vars) witnesses
          else pure false
        | None => pure false end
      else pure false
    | None => pure false end
  | _,_ => pure false end.

Theorem validated_double_reindexed_tiling_loops_at source candidate context vars witnesses swaps parameters before after :
  length parameters = length context -> DoubleAssignmentInstr.NonAlias before ->
  mayReturn (checked_double_reindexed_tiling_loops (source,context,vars) (candidate,context,vars) witnesses swaps) true ->
  DoubleAssignmentIRs.Loop.loop_semantics source (rev parameters) before after ->
  DoubleAssignmentIRs.Loop.loop_semantics candidate (rev parameters) before after.
Proof.
  intros LENGTH NONALIAS CHECK SOURCE_RUN; unfold checked_double_reindexed_tiling_loops in CHECK.
  destruct (DoubleAssignmentExtractor.extractor (source,context,vars)) as [source_program|error] eqn:SOURCE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (DoubleAssignmentExtractor.extractor (candidate,context,vars)) as [candidate_program|error] eqn:CANDIDATE;
    [|destruct source_program as [[pis ctxt] variables]; apply mayReturn_pure in CHECK; discriminate].
  destruct (@DoubleAssignmentExtractor.extractor_success_inv source context vars _ SOURCE) as [source_instructions [_ [_ SOURCE_PROGRAM]]].
  destruct (@DoubleAssignmentExtractor.extractor_success_inv candidate context vars _ CANDIDATE) as [candidate_instructions [_ [_ CANDIDATE_PROGRAM]]].
  subst source_program candidate_program; cbn -[double_attach_tiling_instructions DoubleCandidate.memory_normalized_instructions double_tiling_pinstr_list_eqb double_tiling_current_shape] in CHECK.
  change (@length PL.ident context) with (@length DoubleAssignmentIRs.Loop.ident context) in CHECK.
  destruct (double_attach_tiling_instructions (length context) (DoubleCandidate.memory_normalized_instructions source_instructions)
    (DoubleCandidate.memory_normalized_instructions
      (DoubleCandidate.memory_reindexed_instructions (length context) swaps candidate_instructions)) witnesses) as [tiled|] eqn:ATTACH;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (double_tiling_current_shape tiled) eqn:SHAPE; [|apply mayReturn_pure in CHECK; discriminate].
  apply double_tiling_current_shape_sound in SHAPE.
  bind_imp_destruct CHECK aligned_result ALIGN.
  destruct aligned_result as [aligned|]; [|apply mayReturn_pure in CHECK; discriminate].
  destruct (double_tiling_pinstr_list_eqb (map (PL.current_view_pi (length context)) tiled) aligned) eqn:SAME;
    [|apply mayReturn_pure in CHECK; discriminate].
  apply double_tiling_pinstr_list_eqb_sound in SAME; subst aligned.
  rewrite (@double_tiling_extractor_execution_at candidate context vars candidate_instructions parameters before after CANDIDATE LENGTH).
  rewrite (@DoubleCandidate.memory_reindexed_execution (length context) swaps parameters
    candidate_instructions context vars before after ltac:(symmetry; exact LENGTH) LENGTH
    (@DoubleCandidate.memory_extracted_identity_representation candidate context vars candidate_instructions CANDIDATE)).
  rewrite (@DoubleCandidate.memory_domain_normalization_execution parameters
    (DoubleCandidate.memory_reindexed_instructions (length context) swaps candidate_instructions) context vars before after).
  rewrite (@DoubleCandidate.memory_aligned_domains_execution parameters (map (PL.current_view_pi (length context)) tiled)
    (DoubleCandidate.memory_normalized_instructions
      (DoubleCandidate.memory_reindexed_instructions (length context) swaps candidate_instructions))
    (map (PL.current_view_pi (length context)) tiled) context vars before after
    ltac:(symmetry; exact LENGTH) ALIGN).
  apply (proj2 (@double_tiling_current_view_execution parameters tiled context vars before after LENGTH SHAPE)).
  eapply (DoubleTiling.validated_memory_multiple_tiling_progress_at double_tiling_state_eq_exact); [exact LENGTH|exact NONALIAS|exact CHECK|].
  apply (proj1 (@DoubleCandidate.memory_domain_normalization_execution parameters source_instructions context vars before after)).
  apply (proj1 (@double_tiling_extractor_execution_at source context vars source_instructions parameters before after SOURCE LENGTH)).
  exact SOURCE_RUN.
Qed.

Fixpoint checked_double_reindexed_tiling_choices source candidate witnesses choices :=
  match choices with
  | [] => pure false
  | swaps::rest =>
    BIND valid <- checked_double_reindexed_tiling_loops source candidate witnesses swaps -;
    if valid then pure true else checked_double_reindexed_tiling_choices source candidate witnesses rest
  end.
Lemma checked_double_reindexed_tiling_choices_sound source candidate witnesses choices :
  mayReturn (checked_double_reindexed_tiling_choices source candidate witnesses choices) true ->
  exists swaps, mayReturn (checked_double_reindexed_tiling_loops source candidate witnesses swaps) true.
Proof.
  induction choices as [|swaps rest IH]; cbn; intro RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - bind_imp_destruct RUN valid CHECK; destruct valid.
    + exists swaps; exact CHECK.
    + apply IH; exact RUN.
Qed.

Print Assumptions validated_double_reindexed_tiling_loops_at.
Print Assumptions checked_double_reindexed_tiling_choices_sound.
