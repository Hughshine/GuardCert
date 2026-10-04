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
From GuardMemory Require Import GuardMemoryParamPointerSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem memory_param_pointer_source_footprint source (package : memory_param_pointer_region_package source) counts parameter_values values :
  length counts = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  length parameter_values = length (param_pointer_region_parameters package) ->
  memory_events_footprint (memory_loop_trace
    (memory_scalar_rectangle 0 (length counts) (length (parameter_values++values)) (memory_param_pointer_region_instructions package))
    (counts++(parameter_values++values))) = flat_map
      (fun coordinates => memory_point_footprint (memory_param_pointer_region_instructions package) (coordinates++parameter_values))
      (memory_rectangular_points counts []).
Proof.
  intros LENGTH PARAM_LENGTH; pose proof (@memory_scalar_rectangle_footprint counts (memory_param_pointer_region_instructions package) (parameter_values++values) [] [] eq_refl) as FOOTPRINT.
  cbn [length rev app] in FOOTPRINT; rewrite FOOTPRINT.
  apply memory_flat_map_ext_in; intros coordinates POINT.
  apply memory_rectangular_points_origin in POINT; apply Forall2_length in POINT.
  rewrite app_assoc; unfold memory_param_pointer_region_instructions.
  apply memory_multi_pointer_point_footprint_prefix with
    (limits := param_pointer_region_limits package++param_pointer_region_parameter_limits package)
    (layout := memory_nest_iterators (param_pointer_region_nest package)++param_pointer_region_parameters package) (extent := param_pointer_region_window package).
  - exact (param_pointer_region_operations (param_pointer_region_syntax package)).
  - rewrite !length_app; rewrite <-LENGTH,<-PARAM_LENGTH; f_equal; exact POINT.
Qed.
Print Assumptions memory_param_pointer_source_footprint.
