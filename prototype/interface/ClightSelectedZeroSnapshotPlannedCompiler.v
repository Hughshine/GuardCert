From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Csyntax Csem.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardInterface Require Import ClightLoadedAffineRegionBuilders ClightSelectedCertifiedCompiler ClightAffineZeroSnapshotPlannedRegionBuilders.
Import CoreAlarmed.
Set Implicit Arguments.

(** The existing registry is fixed inside the proved program. All external
    callbacks remain ordinary source metadata or candidate proposals. *)
Definition compile_selected_zero_snapshot_planned_regions prepare chosen word_describe cached_describe
    word_propose affine_describe affine_propose loaded_profile loaded_propose
    snapshot_profile snapshot_propose private_count(program:Csyntax.program) :=
  compile_selected_certified_regions
    (certified_affine_zero_snapshot_planned_extension
      (certified_loaded_polyhedral_builder prepare word_describe cached_describe word_propose
        affine_describe affine_propose loaded_profile loaded_propose)
      snapshot_profile snapshot_propose)chosen private_count program.

Theorem compile_selected_zero_snapshot_planned_regions_correct prepare chosen word_describe cached_describe
    word_propose affine_describe affine_propose loaded_profile loaded_propose
    snapshot_profile snapshot_propose private_count program target :
  mayReturn(compile_selected_zero_snapshot_planned_regions prepare chosen word_describe cached_describe
    word_propose affine_describe affine_propose loaded_profile loaded_propose
    snapshot_profile snapshot_propose private_count program)(OK target) ->
  backward_simulation(Csem.semantics program)(Asm.semantics target).
Proof. apply compile_selected_certified_regions_correct. Qed.

Print Assumptions compile_selected_zero_snapshot_planned_regions_correct.
