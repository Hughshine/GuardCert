From Stdlib Require Import List ZArith.
From compcert.common Require Import AST Memory.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryFiniteFootprint GuardMemoryRectangularFootprint GuardMemoryFootprintCapabilities.
From GuardAffineNest Require Import AffineNestSyntax AffineNestLoopEncoding AffineNestLeafLoop
  AffineNestScanModel AffineNestScanPoints AffineNestScanFootprint.
Import ListNotations.
Set Implicit Arguments.

(** All permissions used by the scan come from execution of the decoded
    source. No memory capability is requested for a merely possible box cell. *)
Theorem affine_scan_source_capabilities nest parameters instructions valuation lower lower_code code tail locations memory final :
  NoDup(affine_nest_iterators nest++parameters) ->
  affine_lower_nest nest [] parameters lower_code
    (L.Seq(affine_leaf_sequence(length(affine_nest_iterators nest))(length parameters) instructions))=Some code ->
  L.eval_expr(map valuation parameters++tail) lower_code=lower ->
  memory_locations_int32 locations ->
  L.loop_semantics code(map valuation parameters++tail)(RuntimeState locations memory)(RuntimeState locations final) ->
  forall point, affine_scan_point nest valuation lower point ->
    Forall(memory_cell_capable locations memory)
      (memory_point_footprint instructions(map point(affine_nest_iterators nest++parameters))).
Proof.
  intros UNIQUE LOWER VALUE INT32 SOURCE point POINT; apply Forall_forall; intros cell MEMBER.
  pose proof(@memory_loop_source_capabilities code(map valuation parameters++tail)
    (RuntimeState locations memory)(RuntimeState locations final) INT32 SOURCE) as CAPABLE.
  assert(FOOTPRINT:In cell(memory_events_footprint(memory_loop_trace code(map valuation parameters++tail)))).
  { pose proof(@affine_scan_source_footprint nest(affine_nest_iterators nest) [] parameters instructions valuation lower
      lower_code code tail eq_refl UNIQUE LOWER VALUE) as EXACT.
    cbn [rev app] in EXACT; rewrite EXACT.
    apply in_flat_map; exists point; split; [apply affine_scan_points_exact; exact POINT|exact MEMBER]. }
  unfold memory_events_footprint in FOOTPRINT; apply in_flat_map in FOOTPRINT as [event [EVENT ACCESS]].
  apply Forall_forall with(x:=event) in CAPABLE; [|exact EVENT].
  apply Forall_forall with(x:=cell) in CAPABLE; [exact CAPABLE|exact ACCESS].
Qed.
Print Assumptions affine_scan_source_capabilities.
