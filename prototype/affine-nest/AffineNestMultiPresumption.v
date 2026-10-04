From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction
  GuardMemoryWindowCells GuardMemoryWindowCrossPointerSeparation GuardMemoryFootprintCapabilities.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard
  AffineNestMultiStaticPackage AffineNestPackageScanFootprint AffineNestScanModel AffineNestScanPoints AffineNestScanAccesses AffineNestScanSeparation.
Import ListNotations.
Set Implicit Arguments.

Definition affine_multi_alias_result proposal temps := affine_scan_separation_result(affine_proposal_nest proposal)
  (affine_word_valuation temps)(affine_word_valuation temps(affine_proposed_iterator proposal))
  (window_multi_pointer_locations temps(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal))
  (affine_scan_accesses(affine_proposed_operations proposal)).
Definition affine_multi_guard_flag parameters proposal state :=
  affine_package_guard_flag parameters proposal state&&affine_multi_alias_result proposal(entry_temps state).

Theorem affine_multi_guard_nonalias source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal) fe ge locals temps memory after final :
  affine_multi_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  GuardMemoryInstr.NonAlias(RuntimeState
    (memory_restrict_locations(memory_footprint_allowed(affine_package_scan_cells parameters proposal temps))
      (window_multi_pointer_locations temps(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal))) memory).
Proof.
  intros ACCEPT SOURCE; unfold affine_multi_guard_flag in ACCEPT; apply andb_true_iff in ACCEPT as [NUMERIC ALIAS].
  pose proof(@affine_package_scan_capabilities source parameters live proposal(affine_multi_guard package)
    (affine_multi_source_loop package) fe ge locals temps memory after final(affine_multi_pointer_private package)
    (affine_multi_source_lower package) NUMERIC SOURCE) as CAPABLE.
  apply window_cross_pointer_separation_suffices; [exact(affine_multi_window_span package)|].
  unfold affine_package_scan_cells; apply affine_scan_separation_sound with(memory:=memory); [|exact ALIAS].
  intros point POINT; apply Forall_forall; intros cell MEMBER.
  apply Forall_forall with(x:=cell) in CAPABLE; [exact CAPABLE|].
  unfold affine_package_scan_cells,affine_scan_cells; apply in_flat_map; exists point; split;
    [apply affine_scan_points_exact; exact POINT|exact MEMBER].
Qed.
Print Assumptions affine_multi_guard_nonalias.
