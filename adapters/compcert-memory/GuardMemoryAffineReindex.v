From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PointWitness.
From polcert.polygen Require Import Result.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops
  GuardMemoryExtractorTrace GuardMemoryExtractorProgress GuardMemoryDomainNormalization GuardMemoryCoordinateSwap
  GuardMemoryCoordinateShift GuardMemoryCoordinateSkew GuardMemoryReindexedExtractor GuardMemoryDomainAlignment.
Import ListNotations.
Set Implicit Arguments.

Inductive memory_affine_reindex :=
| MemoryReindexSwap (position : nat)
| MemoryReindexShift (position : nat) (delta : Z)
| MemoryReindexSkew (target source : nat) (factor : Z).
Definition memory_affine_reindex_step dimension step instructions :=
  match step with
  | MemoryReindexSwap position => memory_swap_instructions (dimension+position)%nat instructions
  | MemoryReindexShift position delta => memory_shift_instructions (dimension+position)%nat delta instructions
  | MemoryReindexSkew target source factor => memory_skew_instructions
      (dimension+target)%nat (dimension+source)%nat factor instructions end.
Lemma memory_affine_reindex_step_representation dimension step instructions :
  Forall (memory_identity_representation dimension) instructions ->
  Forall (memory_identity_representation dimension) (memory_affine_reindex_step dimension step instructions).
Proof.
  intro REPRESENTATIONS; destruct step; unfold memory_affine_reindex_step.
  all: apply Forall_map; eapply Forall_impl; [|exact REPRESENTATIONS].
  - intros pi REP; apply memory_swap_instruction_representation; exact REP.
  - intros pi REP; apply memory_shift_instruction_representation; exact REP.
  - intros pi REP; apply memory_skew_instruction_representation; exact REP.
Qed.
Lemma memory_affine_reindex_step_execution dimension step parameters instructions context vars initial final :
  length parameters = dimension -> Forall (memory_identity_representation dimension) instructions ->
  (PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (memory_affine_reindex_step dimension step instructions,context,vars) initial final).
Proof.
  intros LENGTH REPRESENTATIONS; destruct step; unfold memory_affine_reindex_step.
  - apply memory_coordinate_swap_execution; [lia|rewrite LENGTH; exact REPRESENTATIONS].
  - apply memory_coordinate_shift_execution; [lia|rewrite LENGTH; exact REPRESENTATIONS].
  - apply memory_coordinate_skew_execution; [lia|rewrite LENGTH; exact REPRESENTATIONS].
Qed.
Fixpoint memory_affine_reindexed_instructions dimension steps instructions :=
  match steps with
  | [] => instructions
  | step::rest => memory_affine_reindexed_instructions dimension rest
      (memory_affine_reindex_step dimension step instructions) end.
Theorem memory_affine_reindexed_execution dimension steps parameters instructions context vars initial final :
  length parameters = dimension -> Forall (memory_identity_representation dimension) instructions ->
  (PL.poly_instance_list_semantics parameters (instructions,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (memory_affine_reindexed_instructions dimension steps instructions,context,vars) initial final).
Proof.
  revert instructions; induction steps; intros instructions LENGTH REPRESENTATIONS; cbn; [reflexivity|].
  rewrite (@memory_affine_reindex_step_execution dimension a parameters instructions context vars initial final LENGTH REPRESENTATIONS).
  apply IHsteps; [exact LENGTH|apply memory_affine_reindex_step_representation; exact REPRESENTATIONS].
Qed.
Definition memory_affine_reindex_poly_program steps (program : PL.t) :=
  let '(instructions,context,vars) := program in
  (memory_normalized_instructions (memory_affine_reindexed_instructions (length context) steps instructions),context,vars).
Print Assumptions memory_affine_reindexed_execution.
