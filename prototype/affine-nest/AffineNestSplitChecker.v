From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineReindex GuardMemoryBoundedSourceChecker.
From GuardAffineNest Require Import AffineNestDomainSplit AffineNestBoundedSiteChecker.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.

Definition checked_affine_split_candidate bounds source context pointers candidate conditions steps positions :=
  checked_affine_bounded_site_candidate bounds(affine_partitioned_sources conditions source)
    context pointers candidate steps positions.

Theorem checked_affine_split_candidate_correct bounds source context pointers candidate conditions steps positions :
  mayReturn(checked_affine_split_candidate bounds source context pointers candidate conditions steps positions) true ->
  memory_bounded_source_certificate bounds source context candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  eapply checked_affine_bounded_site_candidate_correct; [exact CHECK|exact LENGTH|exact WITHIN|exact NONALIAS|].
  apply affine_partitioned_sources_execution; exact SOURCE.
Qed.
Print Assumptions checked_affine_split_candidate_correct.
