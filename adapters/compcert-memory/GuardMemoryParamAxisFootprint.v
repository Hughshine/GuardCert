From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Misc.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryPointerSequence
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerCompute GuardMemoryMultiPointerAccess GuardMemoryMultiPointerFootprint
  GuardMemoryMultiPointerProjectedCandidate GuardMemoryLinearPointerSyntax GuardMemoryRecursiveSource
  GuardMemoryRecursiveSyntax GuardMemoryRecursiveDomain GuardMemoryRectangularFootprint GuardMemoryInstructionPadding
  GuardMemoryFiniteFootprint GuardMemoryLoopTrace GuardMemoryScalarLoops.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamPointerFootprint GuardMemoryParamPointerProjectedCandidate.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Export GuardMemoryPointerAccessFootprint.

Definition memory_param_axis_pointer_access_cell := GuardMemoryPointerAccessFootprint.memory_param_axis_pointer_access_cell.
Definition memory_param_axis_pointer_point_footprint := @GuardMemoryPointerAccessFootprint.memory_param_axis_pointer_point_footprint.
Definition memory_param_axis_pointer_parameters := @GuardMemoryPointerAccessFootprint.memory_param_axis_pointer_parameters.

Theorem memory_param_axis_pointer_runtime_footprint source (package : memory_param_pointer_region_package source) temps counts :
  memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest package)) counts temps ->
  Forall signed_range counts ->
  memory_param_pointer_runtime_footprint package temps =
    flat_map (fun coordinates => map (fun access => memory_param_axis_pointer_access_cell access
      (coordinates++memory_recursive_parameters (param_pointer_region_parameters package) temps))
      (memory_linear_pointer_accesses (param_pointer_region_code package))) (memory_rectangular_points counts []).
Proof.
  intros WORDS RANGES.
  assert (DIMENSIONS : length counts = length (memory_nest_iterators (param_pointer_region_nest package))).
  { unfold memory_nest_bindings in WORDS; apply Forall2_length in WORDS.
    rewrite memory_nest_lengths; symmetry; exact WORDS. }
  pose proof (@memory_param_pointer_source_footprint source package counts
    (memory_recursive_parameters (param_pointer_region_parameters package) temps)
    (memory_recursive_parameters (param_pointer_region_scalars package) temps) DIMENSIONS
    ltac:(unfold memory_recursive_parameters; apply length_map)) as FOOTPRINT.
  unfold memory_recursive_parameters in FOOTPRINT; rewrite !length_app,!length_map in FOOTPRINT.
  unfold memory_param_pointer_runtime_footprint,memory_param_pointer_runtime_context,memory_param_pointer_runtime_loop.
  unfold memory_recursive_parameters; rewrite !map_app.
  change (memory_events_footprint (memory_loop_trace
    (memory_scalar_rectangle 0 (length (memory_nest_iterators (param_pointer_region_nest package)))
      (length (param_pointer_region_parameters package++param_pointer_region_scalars package)) (memory_param_pointer_region_instructions package))
    (memory_recursive_parameters (memory_nest_bounds (param_pointer_region_nest package)) temps ++
      (memory_recursive_parameters (param_pointer_region_parameters package) temps++
       memory_recursive_parameters (param_pointer_region_scalars package) temps))) =
    flat_map (fun coordinates => map (fun access => memory_param_axis_pointer_access_cell access
      (coordinates++memory_recursive_parameters (param_pointer_region_parameters package) temps))
      (memory_linear_pointer_accesses (param_pointer_region_code package))) (memory_rectangular_points counts [])).
  rewrite (memory_param_axis_pointer_parameters WORDS RANGES),<-DIMENSIONS.
  unfold memory_recursive_parameters; rewrite length_app; rewrite FOOTPRINT.
  apply memory_flat_map_ext_in; intros coordinates MEMBER.
  unfold memory_param_pointer_region_instructions; apply memory_param_axis_pointer_point_footprint.
Qed.

Theorem memory_param_axis_pointer_footprint_member source (package : memory_param_pointer_region_package source) temps counts cell :
  memory_nest_bindings (memory_nest_bounds (param_pointer_region_nest package)) counts temps ->
  Forall signed_range counts ->
  (In cell (memory_param_pointer_runtime_footprint package temps) <->
    exists access coordinates,
      In access (memory_linear_pointer_accesses (param_pointer_region_code package)) /\
      Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts /\
      cell = memory_param_axis_pointer_access_cell access
        (coordinates++memory_recursive_parameters (param_pointer_region_parameters package) temps)).
Proof.
  intros WORDS RANGES; rewrite (memory_param_axis_pointer_runtime_footprint package WORDS RANGES).
  rewrite in_flat_map; split.
  - intros [coordinates [COORDINATES CELL]].
    apply memory_rectangular_points_origin in COORDINATES; apply in_map_iff in CELL as [access [SAME MEMBER]].
    exists access,coordinates; auto.
  - intros [access [coordinates [MEMBER [COORDINATES ->]]]].
    exists coordinates; split; [apply memory_rectangular_points_origin; exact COORDINATES|].
    apply in_map_iff; exists access; auto.
Qed.

Lemma memory_param_axis_pointer_accesses_valid source (package : memory_param_pointer_region_package source) :
  Forall (memory_multi_pointer_access_valid
    (param_pointer_region_limits package++param_pointer_region_parameter_limits package)
    (memory_nest_iterators (param_pointer_region_nest package)++param_pointer_region_parameters package) (param_pointer_region_window package))
    (memory_linear_pointer_accesses (param_pointer_region_code package)).
Proof.
  pose proof (param_pointer_region_operations (param_pointer_region_syntax package)) as OPS.
  induction OPS as [|operation operations [WRITE [READS VALUE]] REST IH]; cbn [memory_linear_pointer_accesses flat_map].
  - constructor.
  - apply Forall_app; split; [constructor; assumption|exact IH].
Qed.

Lemma memory_param_axis_pointer_accesses_encoding source (package : memory_param_pointer_region_package source) access :
  In access (memory_linear_pointer_accesses (param_pointer_region_code package)) ->
  memory_encode_nary_index (memory_nest_iterators (param_pointer_region_nest package)++param_pointer_region_parameters package)
    (memory_nary_access_expression access) = Some (memory_nary_access_index access).
Proof.
  intro MEMBER; pose proof (memory_param_axis_pointer_accesses_valid package) as VALID.
  apply Forall_forall with (x := access) in VALID; [|exact MEMBER].
  exact (proj1 (proj2 (proj1 VALID))).
Qed.
Print Assumptions memory_param_axis_pointer_runtime_footprint.
Print Assumptions memory_param_axis_pointer_accesses_encoding.

Lemma memory_param_axis_pointer_accesses_covered source (package : memory_param_pointer_region_package source) :
  Forall (fun access => In (memory_nary_access_array access) (param_pointer_region_pointers package))
    (memory_linear_pointer_accesses (param_pointer_region_code package)).
Proof.
  pose proof (param_pointer_region_covered (param_pointer_region_syntax package)) as OPS.
  induction OPS as [|operation operations [WRITE READS] REST IH]; cbn [memory_linear_pointer_accesses flat_map].
  - constructor.
  - apply Forall_app; split; [constructor; assumption|exact IH].
Qed.
