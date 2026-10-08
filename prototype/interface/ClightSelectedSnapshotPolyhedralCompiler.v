From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Csyntax Csem.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardInterface Require Import ClightLoadedAffineRegionBuilders ClightSelectedAffineSnapshotCompiler.
Import CoreAlarmed.
Set Implicit Arguments.

(** The existing registry is fixed inside the proved program. All external
    callbacks remain ordinary source metadata or candidate proposals. *)
Definition compile_selected_snapshot_polyhedral_regions prepare chosen word_describe cached_describe
    word_propose affine_describe affine_propose loaded_profile loaded_propose
    snapshot_profile snapshot_propose private_count(program:Csyntax.program) :=
  compile_selected_affine_snapshot_regions
    (certified_loaded_polyhedral_builder prepare word_describe cached_describe word_propose
      affine_describe affine_propose loaded_profile loaded_propose)
    snapshot_profile snapshot_propose chosen private_count program.

Theorem compile_selected_snapshot_polyhedral_regions_correct prepare chosen word_describe cached_describe
    word_propose affine_describe affine_propose loaded_profile loaded_propose
    snapshot_profile snapshot_propose private_count program target :
  mayReturn(compile_selected_snapshot_polyhedral_regions prepare chosen word_describe cached_describe
    word_propose affine_describe affine_propose loaded_profile loaded_propose
    snapshot_profile snapshot_propose private_count program)(OK target) ->
  backward_simulation(Csem.semantics program)(Asm.semantics target).
Proof. apply compile_selected_affine_snapshot_regions_correct. Qed.

Print Assumptions compile_selected_snapshot_polyhedral_regions_correct.
