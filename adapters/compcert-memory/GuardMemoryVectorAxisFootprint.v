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
From GuardMemory Require Import GuardMemoryVectorPointerSyntax GuardMemoryVectorPointerFootprint GuardMemoryVectorPointerProjectedCandidate.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_vector_axis_pointer_access_cell access coordinates :=
  point_cell (memory_nary_access_array access) (memory_nary_index_value (memory_nary_access_index access) coordinates).

Lemma memory_vector_axis_pointer_point_footprint extra operations coordinates :
  memory_point_footprint (memory_pad_instructions extra (map memory_nary_compute_instruction operations)) coordinates =
    map (fun access => memory_vector_axis_pointer_access_cell access coordinates) (memory_linear_pointer_accesses operations).
Proof.
  induction operations as [|operation operations IH]; [reflexivity|].
  cbn [memory_point_footprint memory_pad_instructions map flat_map].
  rewrite memory_pad_instruction_footprint.
  change (memory_instruction_footprint (memory_nary_compute_instruction operation) coordinates ++
    memory_point_footprint (memory_pad_instructions extra (map memory_nary_compute_instruction operations)) coordinates =
      map (fun access => memory_vector_axis_pointer_access_cell access coordinates) (memory_linear_pointer_accesses (operation::operations))).
  rewrite IH; unfold memory_linear_pointer_accesses; cbn [flat_map]; rewrite map_app; f_equal.
  unfold memory_instruction_footprint; cbn [memory_nary_compute_instruction instruction_write instruction_reads].
  rewrite map_map; reflexivity.
Qed.

Lemma memory_vector_axis_pointer_parameters identifiers values temps :
  memory_nest_bindings identifiers values temps -> Forall signed_range values ->
  memory_recursive_parameters identifiers temps = values.
Proof.
  intro WORDS; induction WORDS as [|identifier value identifiers values WORD WORDS IH]; intro RANGES.
  - reflexivity.
  - inversion RANGES; subst; unfold memory_recursive_parameters at 1; cbn [map].
    unfold temp_word at 1; rewrite WORD,Int.signed_repr by assumption.
    f_equal; apply IH; assumption.
Qed.

Theorem memory_vector_axis_pointer_runtime_footprint source (package : memory_vector_pointer_region_package source) temps counts :
  memory_nest_bindings (memory_nest_bounds (vector_pointer_region_nest package)) counts temps ->
  Forall signed_range counts ->
  memory_vector_pointer_runtime_footprint package temps =
    flat_map (fun coordinates => map (fun access => memory_vector_axis_pointer_access_cell access coordinates)
      (memory_linear_pointer_accesses (vector_pointer_region_code package))) (memory_rectangular_points counts []).
Proof.
  intros WORDS RANGES.
  assert (DIMENSIONS : length counts = length (memory_nest_iterators (vector_pointer_region_nest package))).
  { unfold memory_nest_bindings in WORDS; apply Forall2_length in WORDS.
    rewrite memory_nest_lengths; symmetry; exact WORDS. }
  pose proof (@memory_vector_pointer_source_footprint source package counts
    (memory_recursive_parameters (vector_pointer_region_scalars package) temps) DIMENSIONS) as FOOTPRINT.
  unfold memory_recursive_parameters in FOOTPRINT; rewrite length_map in FOOTPRINT.
  unfold memory_vector_pointer_runtime_footprint,memory_vector_pointer_runtime_context,memory_vector_pointer_runtime_loop.
  unfold memory_recursive_parameters; rewrite map_app.
  change (memory_events_footprint (memory_loop_trace
    (memory_scalar_rectangle 0 (length (memory_nest_iterators (vector_pointer_region_nest package)))
      (length (vector_pointer_region_scalars package)) (memory_vector_pointer_region_instructions package))
    (memory_recursive_parameters (memory_nest_bounds (vector_pointer_region_nest package)) temps ++
      memory_recursive_parameters (vector_pointer_region_scalars package) temps)) =
    flat_map (fun coordinates => map (fun access => memory_vector_axis_pointer_access_cell access coordinates)
      (memory_linear_pointer_accesses (vector_pointer_region_code package))) (memory_rectangular_points counts [])).
  rewrite (memory_vector_axis_pointer_parameters WORDS RANGES),<-DIMENSIONS.
  unfold memory_recursive_parameters; rewrite FOOTPRINT.
  apply memory_flat_map_ext_in; intros coordinates MEMBER.
  unfold memory_vector_pointer_region_instructions; apply memory_vector_axis_pointer_point_footprint.
Qed.

Theorem memory_vector_axis_pointer_footprint_member source (package : memory_vector_pointer_region_package source) temps counts cell :
  memory_nest_bindings (memory_nest_bounds (vector_pointer_region_nest package)) counts temps ->
  Forall signed_range counts ->
  (In cell (memory_vector_pointer_runtime_footprint package temps) <->
    exists access coordinates,
      In access (memory_linear_pointer_accesses (vector_pointer_region_code package)) /\
      Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts /\
      cell = memory_vector_axis_pointer_access_cell access coordinates).
Proof.
  intros WORDS RANGES; rewrite (memory_vector_axis_pointer_runtime_footprint package WORDS RANGES).
  rewrite in_flat_map; split.
  - intros [coordinates [COORDINATES CELL]].
    apply memory_rectangular_points_origin in COORDINATES; apply in_map_iff in CELL as [access [SAME MEMBER]].
    exists access,coordinates; auto.
  - intros [access [coordinates [MEMBER [COORDINATES ->]]]].
    exists coordinates; split; [apply memory_rectangular_points_origin; exact COORDINATES|].
    apply in_map_iff; exists access; auto.
Qed.

Lemma memory_vector_axis_pointer_accesses_valid source (package : memory_vector_pointer_region_package source) :
  Forall (memory_multi_pointer_access_valid
    (vector_pointer_region_limits package)
    (memory_nest_iterators (vector_pointer_region_nest package)) (vector_pointer_region_window package))
    (memory_linear_pointer_accesses (vector_pointer_region_code package)).
Proof.
  pose proof (vector_pointer_region_operations (vector_pointer_region_syntax package)) as OPS.
  induction OPS as [|operation operations [WRITE [READS VALUE]] REST IH]; cbn [memory_linear_pointer_accesses flat_map].
  - constructor.
  - apply Forall_app; split; [constructor; assumption|exact IH].
Qed.

Lemma memory_vector_axis_pointer_accesses_encoding source (package : memory_vector_pointer_region_package source) access :
  In access (memory_linear_pointer_accesses (vector_pointer_region_code package)) ->
  memory_encode_nary_index (memory_nest_iterators (vector_pointer_region_nest package))
    (memory_nary_access_expression access) = Some (memory_nary_access_index access).
Proof.
  intro MEMBER; pose proof (memory_vector_axis_pointer_accesses_valid package) as VALID.
  apply Forall_forall with (x := access) in VALID; [|exact MEMBER].
  exact (proj1 (proj2 (proj1 VALID))).
Qed.
Print Assumptions memory_vector_axis_pointer_runtime_footprint.
Print Assumptions memory_vector_axis_pointer_accesses_encoding.

Lemma memory_vector_axis_pointer_accesses_covered source (package : memory_vector_pointer_region_package source) :
  Forall (fun access => In (memory_nary_access_array access) (vector_pointer_region_pointers package))
    (memory_linear_pointer_accesses (vector_pointer_region_code package)).
Proof.
  pose proof (vector_pointer_region_covered (vector_pointer_region_syntax package)) as OPS.
  induction OPS as [|operation operations [WRITE READS] REST IH]; cbn [memory_linear_pointer_accesses flat_map].
  - constructor.
  - apply Forall_app; split; [constructor; assumption|exact IH].
Qed.
