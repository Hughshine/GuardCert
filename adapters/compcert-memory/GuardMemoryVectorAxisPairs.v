From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate GuardMemoryLinearPointerSyntax
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryFiniteFootprint
  GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities GuardMemoryFootprintRestriction
  GuardMemoryCrossPointerSeparation GuardMemoryAffinePointerPairs GuardMemoryRecursiveSource.
From GuardMemory Require Import GuardMemoryAxisPointerFootprint GuardMemoryAffineAxisPairScan
  GuardMemoryBooleanRectangle.
From GuardMemory Require Import GuardMemoryVectorPointerSyntax GuardMemoryVectorPointerProjectedCandidate GuardMemoryVectorAxisFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_vector_axis_access_pair_check locations counts pair :=
  memory_affine_axis_pair_check locations counts
    (memory_nary_access_array (fst pair)) (memory_nary_access_array (snd pair))
    (memory_nary_access_index (fst pair)) (memory_nary_access_index (snd pair)).
Definition memory_vector_axis_pointer_pairs_check source (package : memory_vector_pointer_region_package source) locations counts :=
  forallb (memory_vector_axis_access_pair_check locations counts)
    (memory_affine_access_pairs (memory_linear_pointer_accesses (vector_pointer_region_code package))).

Theorem memory_vector_axis_pointer_access_capability source (package : memory_vector_pointer_region_package source)
  temps memory counts :
  memory_nest_bindings (memory_nest_bounds (vector_pointer_region_nest package)) counts temps ->
  Forall signed_range counts ->
  Forall (memory_cell_capable (memory_multi_pointer_locations temps (vector_pointer_region_window package)) memory)
    (memory_vector_pointer_runtime_footprint package temps) ->
  forall access coordinates,
    In access (memory_linear_pointer_accesses (vector_pointer_region_code package)) ->
    Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
    memory_cell_capable (memory_multi_pointer_locations temps (vector_pointer_region_window package)) memory
      (memory_vector_axis_pointer_access_cell access coordinates).
Proof.
  intros WORDS RANGES CELLS access coordinates MEMBER COORDINATES.
  apply Forall_forall with (x := memory_vector_axis_pointer_access_cell access coordinates) in CELLS; [exact CELLS|].
  apply (proj2 (@memory_vector_axis_pointer_footprint_member source package temps counts _ WORDS RANGES)).
  exists access,coordinates; auto.
Qed.

Theorem memory_vector_axis_pointer_pairs_separation source (package : memory_vector_pointer_region_package source)
  (ge : genv) (locals : env) temps memory counts :
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  memory_nest_bindings (memory_nest_bounds (vector_pointer_region_nest package)) counts temps ->
  Forall (memory_cell_capable (memory_multi_pointer_locations temps (vector_pointer_region_window package)) memory)
    (memory_vector_pointer_runtime_footprint package temps) ->
  memory_vector_axis_pointer_pairs_check package (memory_multi_pointer_locations temps (vector_pointer_region_window package)) counts = true ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_vector_pointer_runtime_footprint package temps))
    (memory_multi_pointer_locations temps (vector_pointer_region_window package))).
Proof.
  intros RANGES WORDS CELLS CHECK.
  assert (SIGNED : Forall signed_range counts).
  { eapply Forall_impl; [|exact RANGES]; intros count [POS RANGE]; exact RANGE. }
  assert (NONNEG : Forall (fun count => 0 <= count) counts).
  { eapply Forall_impl; [|exact RANGES]; intros count [POS RANGE]; exact POS. }
  apply memory_cross_pointer_separation_suffices.
  - exact (proj2 (proj2 (vector_pointer_region_extent (vector_pointer_region_syntax package)))).
  - intros first second left right FIRST_MEMBER SECOND_MEMBER DISTINCT FIRST SECOND.
    apply memory_footprint_allowed_exact in FIRST_MEMBER,SECOND_MEMBER.
    pose proof FIRST_MEMBER as FIRST_FOOTPRINT; pose proof SECOND_MEMBER as SECOND_FOOTPRINT.
    apply (proj1 (@memory_vector_axis_pointer_footprint_member source package temps counts first WORDS SIGNED))
      in FIRST_MEMBER as [first_access [first_coordinates [FIRST_ACCESS [FIRST_RANGE ->]]]].
    apply (proj1 (@memory_vector_axis_pointer_footprint_member source package temps counts second WORDS SIGNED))
      in SECOND_MEMBER as [second_access [second_coordinates [SECOND_ACCESS [SECOND_RANGE ->]]]].
    unfold memory_vector_axis_pointer_pairs_check in CHECK.
    apply forallb_forall with (x := (first_access,second_access)) in CHECK.
    2: { apply memory_affine_access_pair_member; repeat split; assumption. }
    unfold memory_vector_axis_access_pair_check,memory_affine_axis_pair_check in CHECK; cbn [fst snd] in CHECK.
    rewrite memory_boolean_rectangle_member in CHECK by exact NONNEG.
    specialize (CHECK first_coordinates FIRST_RANGE); cbn [app] in CHECK.
    rewrite memory_boolean_rectangle_member in CHECK by exact NONNEG.
    specialize (CHECK second_coordinates SECOND_RANGE); cbn [app] in CHECK.
    assert (FIRST_CAP : memory_cell_address_binding memory_multi_pointer_cell_code
      (memory_multi_pointer_locations temps (vector_pointer_region_window package))
      (Entry ge locals temps memory) (memory_vector_axis_pointer_access_cell first_access first_coordinates)).
    { apply memory_multi_pointer_cell_encoding;
      [exact (proj1 (proj2 (vector_pointer_region_extent (vector_pointer_region_syntax package))))|].
      apply Forall_forall with (x := memory_vector_axis_pointer_access_cell first_access first_coordinates) in CELLS; assumption. }
    assert (SECOND_CAP : memory_cell_address_binding memory_multi_pointer_cell_code
      (memory_multi_pointer_locations temps (vector_pointer_region_window package))
      (Entry ge locals temps memory) (memory_vector_axis_pointer_access_cell second_access second_coordinates)).
    { apply memory_multi_pointer_cell_encoding;
      [exact (proj1 (proj2 (vector_pointer_region_extent (vector_pointer_region_syntax package))))|].
      apply Forall_forall with (x := memory_vector_axis_pointer_access_cell second_access second_coordinates) in CELLS; assumption. }
    eapply memory_cell_pair_address_separated; [exact FIRST_CAP|exact SECOND_CAP|exact FIRST|exact SECOND| |exact CHECK].
    left; exact DISTINCT.
Qed.
Print Assumptions memory_vector_axis_pointer_pairs_separation.
