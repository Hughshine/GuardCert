From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryFiniteFootprint
  GuardMemoryRectangularFootprint GuardMemoryFootprintCapabilities GuardMemoryNaryCompute GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard AffineNestPackageDecode AffineNestSourceDecode
  AffineNestRealDecode AffineNestLeafDecode AffineNestLeafModel AffineNestScanModel AffineNestScanPoints
  AffineNestScanAccesses AffineNestScanFootprint AffineNestScanCapabilities AffineNestScanSeparation.
Import ListNotations.
Set Implicit Arguments.

Definition affine_package_scan_cells (parameters:list ident) proposal temps :=
  affine_scan_cells(affine_proposal_nest proposal)(affine_word_valuation temps)
    (affine_word_valuation temps(affine_proposed_iterator proposal))(affine_scan_accesses(affine_proposed_operations proposal)).

Theorem affine_package_scan_footprint source parameters live proposal
  (package:affine_guard_package source parameters live proposal) source_loop temps :
  affine_package_source_loop parameters proposal=Some source_loop ->
  memory_events_footprint(memory_loop_trace source_loop(map(affine_word_valuation temps)(affine_package_context parameters proposal)))=
    affine_package_scan_cells parameters proposal temps.
Proof.
  intro LOWER.
  pose proof(affine_leaf_unique(affine_package_leaf package)) as UNIQUE; rewrite app_nil_r in UNIQUE.
  unfold affine_package_source_loop,affine_checked_nest_loop,affine_checked_leaf_code in LOWER; rewrite !app_nil_r in LOWER.
  assert(VALUE:L.eval_expr(map(affine_word_valuation temps) parameters++
    [affine_word_valuation temps(affine_proposed_iterator proposal)])(L.Var(length parameters))=
    affine_word_valuation temps(affine_proposed_iterator proposal)).
  { cbn [L.eval_expr]; rewrite <-length_map with(f:=affine_word_valuation temps)(l:=parameters); apply nth_middle. }
  pose proof(@affine_scan_source_footprint(affine_proposal_nest proposal)(affine_nest_iterators(affine_proposal_nest proposal))
    [] parameters(map memory_nary_compute_instruction(affine_proposed_operations proposal))(affine_word_valuation temps)
    (affine_word_valuation temps(affine_proposed_iterator proposal))(L.Var(length parameters)) source_loop
    [affine_word_valuation temps(affine_proposed_iterator proposal)] eq_refl UNIQUE LOWER VALUE) as EXACT.
  unfold affine_package_context; rewrite map_app; cbn [map]; cbn [rev app] in EXACT; rewrite EXACT.
  unfold affine_package_scan_cells,affine_scan_cells.
  apply flat_map_ext; intro point; apply affine_scan_point_footprint with
    (bounds:=affine_proposed_leaf_bounds proposal)(lower:=affine_proposed_window_lower proposal)
    (upper:=affine_proposed_window_upper proposal)(scalars:=[]).
  exact(affine_leaf_valid(affine_package_leaf package)).
Qed.

Theorem affine_package_scan_capabilities source parameters live proposal
  (package:affine_guard_package source parameters live proposal) source_loop fe ge locals temps memory after final :
  (forall pointer, In pointer(affine_proposed_pointers proposal) -> ~In pointer(affine_nest_mutated(affine_proposal_nest proposal))) ->
  affine_package_source_loop parameters proposal=Some source_loop ->
  affine_package_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  Forall(memory_cell_capable(window_multi_pointer_locations temps(affine_proposed_window_lower proposal)
    (affine_proposed_window_upper proposal)) memory)(affine_package_scan_cells parameters proposal temps).
Proof.
  intros PRIVATE LOWER ACCEPT SOURCE.
  pose proof(@affine_package_source_decode source parameters live proposal package source_loop fe ge locals temps memory after final
    PRIVATE LOWER ACCEPT SOURCE) as LOOP.
  pose proof(@memory_loop_source_capabilities source_loop(map(affine_word_valuation temps)(affine_package_context parameters proposal))
    (RuntimeState(window_multi_pointer_locations temps(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)) memory)
    (RuntimeState(window_multi_pointer_locations temps(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)) final)
    (window_multi_pointer_locations_int32 temps(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)) LOOP) as CAPABLE.
  rewrite <-(affine_package_scan_footprint package temps LOWER).
  apply Forall_forall; intros cell MEMBER; unfold memory_events_footprint in MEMBER.
  apply in_flat_map in MEMBER as [event [EVENT ACCESS]].
  apply Forall_forall with(x:=event) in CAPABLE; [|exact EVENT].
  apply Forall_forall with(x:=cell) in CAPABLE; [exact CAPABLE|exact ACCESS].
Qed.
Print Assumptions affine_package_scan_footprint.
Print Assumptions affine_package_scan_capabilities.
