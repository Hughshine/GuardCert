From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightSkipPrefix ClightTempFootprint.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl GuardMemoryLongProgressControl
  GuardMemoryDoubleMatmul.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulDoubleLowering Require Import OriginalMatmulDoubleLowering.
From GuardInterface Require Import OriginalMatmulRawSource.

(** The actual frontend's administrative steps are related to the existing
    model source. Runtime fallback keeps that actual source statement. *)
Lemma original_matmul_raw_source_relation : skip_prefix_relation raw_original_matmul_region original_matmul_region.
Proof.
  rewrite original_matmul_raw_frontend_shape; unfold raw_original_long_loop,original_matmul_region,original_long_loop.
  repeat constructor.
Qed.
Theorem original_matmul_raw_source_execution :
  statement_execution_equivalent raw_original_matmul_region original_matmul_region.
Proof. apply skip_prefix_execution_equivalent, original_matmul_raw_source_relation. Qed.
Lemma original_matmul_raw_temporary_footprint :
  statement_temps raw_original_matmul_region=statement_temps original_matmul_region.
Proof. apply skip_prefix_temporary_footprint, original_matmul_raw_source_relation. Qed.
Theorem original_matmul_raw_guarded_execution code :
  statement_execution_equivalent (original_matmul_guarded_code raw_original_matmul_region code)
    (original_matmul_guarded_code original_matmul_region code).
Proof.
  apply skip_prefix_execution_equivalent; unfold original_matmul_guarded_code.
  apply skip_prefix_sequence; [constructor|].
  apply skip_prefix_choice; [constructor|exact original_matmul_raw_source_relation].
Qed.

Print Assumptions original_matmul_raw_source_execution.
Print Assumptions original_matmul_raw_temporary_footprint.
Print Assumptions original_matmul_raw_guarded_execution.
