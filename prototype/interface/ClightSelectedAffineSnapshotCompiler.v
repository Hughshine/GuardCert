From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Csyntax Csem.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardInterface Require Import ClightCertifiedRegionBuilder ClightSelectedCertifiedCompiler
  ClightAffineSnapshotRegionBuilders.
Import CoreAlarmed.
Set Implicit Arguments.

Definition compile_selected_affine_snapshot_regions existing profile propose chosen private_count
    (program:Csyntax.program) :=
  compile_selected_certified_regions(certified_affine_snapshot_extension existing profile propose)
    chosen private_count program.
Theorem compile_selected_affine_snapshot_regions_correct existing profile propose chosen private_count program target :
  mayReturn(compile_selected_affine_snapshot_regions existing profile propose chosen private_count program)(OK target) ->
  backward_simulation(Csem.semantics program)(Asm.semantics target).
Proof. apply compile_selected_certified_regions_correct. Qed.

Print Assumptions compile_selected_affine_snapshot_regions_correct.
