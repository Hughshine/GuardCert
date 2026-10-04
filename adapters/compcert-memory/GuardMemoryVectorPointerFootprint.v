From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryNaryCompute
  GuardMemoryNaryAffineAccess GuardMemoryNaryAccessCheck GuardMemoryScalarAccess GuardMemoryInstructionPadding
  GuardMemoryMultiPointerCompute GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerCells GuardMemoryMultiPointerDomain
  GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveDomain GuardMemoryRectangularFootprint GuardMemoryScalarLoops
  GuardMemoryActivatedRectangle GuardMemoryActivatedAliasCondition GuardMemoryFootprintCapabilities GuardMemoryFiniteFootprint.
From GuardMemory Require Import GuardMemoryMultiPointerFootprint.
From GuardMemory Require Import GuardMemoryVectorPointerSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_vector_pointer_source_footprint source (package : memory_vector_pointer_region_package source) counts values :
  length counts = length (memory_nest_iterators (vector_pointer_region_nest package)) ->
  memory_events_footprint (memory_loop_trace
    (memory_scalar_rectangle 0 (length counts) (length values) (memory_vector_pointer_region_instructions package))
    (counts++values)) = flat_map (memory_point_footprint (memory_vector_pointer_region_instructions package))
      (memory_rectangular_points counts []).
Proof.
  intro LENGTH; pose proof (@memory_scalar_rectangle_footprint counts (memory_vector_pointer_region_instructions package) values [] [] eq_refl) as FOOTPRINT.
  cbn [length rev app] in FOOTPRINT; rewrite FOOTPRINT.
  apply memory_flat_map_ext_in; intros coordinates POINT.
  apply memory_rectangular_points_origin in POINT; apply Forall2_length in POINT.
  unfold memory_vector_pointer_region_instructions.
  apply memory_multi_pointer_point_footprint_prefix with
    (limits := vector_pointer_region_limits package)
    (layout := memory_nest_iterators (vector_pointer_region_nest package)) (extent := vector_pointer_region_window package).
  - exact (vector_pointer_region_operations (vector_pointer_region_syntax package)).
  - lia.
Qed.
Print Assumptions memory_vector_pointer_source_footprint.
