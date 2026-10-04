From Stdlib Require Import List ZArith.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.src Require Import TilingWitness.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineReindex
  GuardMemoryBoundedSourceChecker GuardMemoryBoundedSourceTiling.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.

(** Candidate evidence selects a proved validator. Both descriptions remain
    untrusted: the extracted checks establish the same source certificate. *)
Inductive affine_candidate_evidence :=
  | AffineIndexEvidence (steps : list memory_affine_reindex)
  | AffineTilingEvidence (witnesses : list statement_tiling_witness).

Definition checked_affine_candidate bounds source context pointers candidate evidence :=
  match evidence with
  | AffineIndexEvidence steps =>
      checked_memory_bounded_source_candidate bounds source context pointers candidate steps
  | AffineTilingEvidence witnesses =>
      checked_memory_bounded_source_tiling bounds source candidate context pointers witnesses
  end.

Theorem checked_affine_candidate_correct bounds source context pointers candidate evidence :
  mayReturn(checked_affine_candidate bounds source context pointers candidate evidence) true ->
  memory_bounded_source_certificate bounds source context candidate.
Proof.
  destruct evidence as [steps|witnesses]; cbn [checked_affine_candidate].
  - apply checked_memory_bounded_source_candidate_correct.
  - apply checked_memory_bounded_source_tiling_correct.
Qed.
Print Assumptions checked_affine_candidate_correct.
