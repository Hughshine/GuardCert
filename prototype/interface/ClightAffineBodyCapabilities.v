From Stdlib Require Import List ZArith.
From compcert.common Require Import AST Memory.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryFiniteFootprint GuardMemoryRectangularFootprint GuardMemoryFootprintCapabilities.
From GuardAffineNest Require Import AffineNestSyntax AffineNestLoopEncoding AffineNestLeafLoop
  AffineNestScanModel AffineNestScanPoints AffineNestScanFootprint.
From GuardInterface Require Import ClightStorePermissions ClightCellCapabilityTransport.
Import ListNotations.
Set Implicit Arguments.

(** Generalize the original full-root capability consumer to a checked child
    model with an enclosing-coordinate prefix. The only execution premise is
    this complete child/body; later loaded root iterations are absent. *)
Theorem affine_prefix_source_capabilities nest coordinates prefix parameters instructions valuation lower lower_code code tail
  locations memory final :
  coordinates=prefix++affine_nest_iterators nest -> NoDup(coordinates++parameters) ->
  affine_lower_nest nest prefix parameters lower_code
    (L.Seq(affine_leaf_sequence(length coordinates)(length parameters) instructions))=Some code ->
  L.eval_expr(map valuation(rev prefix++parameters)++tail) lower_code=lower ->
  memory_locations_int32 locations ->
  L.loop_semantics code(map valuation(rev prefix++parameters)++tail)
    (RuntimeState locations memory)(RuntimeState locations final) ->
  forall point, affine_scan_point nest valuation lower point ->
    Forall(memory_cell_capable locations memory)(memory_point_footprint instructions(map point(coordinates++parameters))).
Proof.
  intros COORDINATES UNIQUE LOWER VALUE INT32 SOURCE point POINT.
  apply Forall_forall; intros cell MEMBER.
  pose proof(@memory_loop_source_capabilities code(map valuation(rev prefix++parameters)++tail)
    (RuntimeState locations memory)(RuntimeState locations final) INT32 SOURCE) as CAPABLE.
  assert(FOOTPRINT:In cell(memory_events_footprint(memory_loop_trace code(map valuation(rev prefix++parameters)++tail)))).
  { rewrite (@affine_scan_source_footprint nest coordinates prefix parameters instructions valuation lower lower_code code tail
      COORDINATES UNIQUE LOWER VALUE).
    apply in_flat_map; exists point; split; [apply affine_scan_points_exact; exact POINT|exact MEMBER]. }
  unfold memory_events_footprint in FOOTPRINT; apply in_flat_map in FOOTPRINT as [event [EVENT ACCESS]].
  apply Forall_forall with(x:=event) in CAPABLE; [|exact EVENT].
  apply Forall_forall with(x:=cell) in CAPABLE; [exact CAPABLE|exact ACCESS].
Qed.

Theorem affine_prefix_capabilities_at_guard_entry nest coordinates prefix parameters instructions valuation lower lower_code code tail
  locations initial memory final :
  coordinates=prefix++affine_nest_iterators nest -> NoDup(coordinates++parameters) ->
  affine_lower_nest nest prefix parameters lower_code
    (L.Seq(affine_leaf_sequence(length coordinates)(length parameters) instructions))=Some code ->
  L.eval_expr(map valuation(rev prefix++parameters)++tail) lower_code=lower ->
  memory_locations_int32 locations -> memory_accesses_back initial memory ->
  L.loop_semantics code(map valuation(rev prefix++parameters)++tail)
    (RuntimeState locations memory)(RuntimeState locations final) ->
  forall point, affine_scan_point nest valuation lower point ->
    Forall(memory_cell_capable locations initial)(memory_point_footprint instructions(map point(coordinates++parameters))).
Proof.
  intros COORDINATES UNIQUE LOWER VALUE INT32 BACK SOURCE point POINT.
  eapply Forall_impl; [|eapply affine_prefix_source_capabilities; eassumption].
  intros cell CAPABLE; eapply cell_capability_accesses_back; eassumption.
Qed.

Print Assumptions affine_prefix_source_capabilities.
Print Assumptions affine_prefix_capabilities_at_guard_entry.
