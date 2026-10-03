From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities GuardMemoryBufferOffsets
  GuardMemoryPointerCellComparison GuardMemoryNaryAffineExpressions GuardMemoryAffineAxisAddress
  GuardMemoryAffineSourceExpressions GuardMemoryRecursiveSource.
From GuardMemory Require Import GuardMemoryAxisBoundaryMath GuardMemoryAxisBoundaryNames
  GuardMemoryAxisRepeatedAddress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_axis_boundary_test layout counters zero mask first second first_expression second_expression :=
  memory_pointer_cells_test
    (memory_affine_axis_address first layout (memory_axis_boundary_names mask counters zero) first_expression)
    (memory_affine_axis_address second layout (memory_axis_boundary_names (map negb mask) counters zero) second_expression).

Definition memory_affine_axis_boundary_coordinate_check locations first second first_term second_term mask coordinates :=
  memory_cell_pair_address_check locations
    (point_cell first (memory_nary_index_value first_term (memory_axis_boundary_pick mask coordinates)))
    (point_cell second (memory_nary_index_value second_term (memory_axis_boundary_pick (map negb mask) coordinates))).

Theorem memory_affine_axis_boundary_test_evaluation first_expression second_expression first_term second_term
  layout counters coordinates counts mask zero ge locals original current memory extent first second :
  memory_encode_nary_index layout first_expression = Some first_term ->
  memory_encode_nary_index layout second_expression = Some second_term ->
  NoDup layout -> length layout = length counters -> length mask = length counts ->
  Forall signed_range counts -> Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
  first <> second -> extent <= Int.max_signed+1 ->
  current ! first = original ! first -> current ! second = original ! second ->
  memory_nest_bindings counters coordinates current -> current ! zero = Some (Vint Int.zero) ->
  (forall point, Forall2 (fun coordinate count => 0 <= coordinate < count) point counts ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell first (memory_nary_index_value first_term point)) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell second (memory_nary_index_value second_term point))) ->
  expression_test (memory_affine_axis_boundary_test layout counters zero mask first second first_expression second_expression)
    (Entry ge locals current memory)
    (memory_affine_axis_boundary_coordinate_check (memory_multi_pointer_locations original extent)
      first second first_term second_term mask coordinates).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE SOURCE_LENGTH MASK SIGNED COORDINATES
    DISTINCT EXTENT FIRST SECOND WORDS ZERO CAPS.
  assert (COORD_LENGTH : length coordinates = length counts) by exact (Forall2_length COORDINATES).
  assert (COUNTER_LENGTH : length counters = length coordinates) by (unfold memory_nest_bindings in WORDS; exact (Forall2_length WORDS)).
  assert (LEFT_RANGE : Forall2 (fun coordinate count => 0 <= coordinate < count)
    (memory_axis_boundary_pick mask coordinates) counts) by (apply memory_axis_boundary_pick_range; assumption).
  assert (RIGHT_RANGE : Forall2 (fun coordinate count => 0 <= coordinate < count)
    (memory_axis_boundary_pick (map negb mask) coordinates) counts).
  { apply memory_axis_boundary_pick_range; [exact COORDINATES|rewrite length_map; exact MASK]. }
  destruct (@memory_affine_axis_repeated_address_binding first_expression first_term layout
    (memory_axis_boundary_names mask counters zero) (memory_axis_boundary_pick mask coordinates)
    ge locals original current memory extent first FIRST_ENCODE SOURCE_UNIQUE
    ltac:(rewrite memory_axis_boundary_names_length by lia; exact SOURCE_LENGTH) EXTENT FIRST
    ltac:(apply memory_axis_boundary_names_bindings; [exact WORDS|lia|exact ZERO])
    (memory_axis_rectangle_coordinates_signed SIGNED LEFT_RANGE) (proj1 (CAPS _ LEFT_RANGE)))
    as [left [left_offset [LEFT [LEFT_CHUNK [LEFT_OFFSET [LEFT_PURE [LEFT_TYPE [LEFT_VALUE [LEFT_VALID LEFT_ALIGN]]]]]]]]].
  destruct (@memory_affine_axis_repeated_address_binding second_expression second_term layout
    (memory_axis_boundary_names (map negb mask) counters zero) (memory_axis_boundary_pick (map negb mask) coordinates)
    ge locals original current memory extent second SECOND_ENCODE SOURCE_UNIQUE
    ltac:(rewrite memory_axis_boundary_names_length by (rewrite length_map; lia); exact SOURCE_LENGTH) EXTENT SECOND
    ltac:(apply memory_axis_boundary_names_bindings; [exact WORDS|rewrite length_map; lia|exact ZERO])
    (memory_axis_rectangle_coordinates_signed SIGNED RIGHT_RANGE) (proj2 (CAPS _ RIGHT_RANGE)))
    as [right [right_offset [RIGHT [RIGHT_CHUNK [RIGHT_OFFSET [RIGHT_PURE [RIGHT_TYPE [RIGHT_VALUE [RIGHT_VALID RIGHT_ALIGN]]]]]]]]].
  unfold memory_affine_axis_boundary_coordinate_check,memory_cell_pair_address_check;
    destruct memory_cell_identity_dec as [SAME|].
  - apply (f_equal arr_id) in SAME; cbn [arr_id point_cell] in SAME; contradiction.
  - rewrite LEFT,RIGHT,LEFT_OFFSET,RIGHT_OFFSET,<-memory_pointer_eq_unsigned.
    exact (@memory_pointer_cells_test_evaluation ge locals current memory _ _ _ _ _ _
      LEFT_TYPE RIGHT_TYPE LEFT_VALUE RIGHT_VALUE LEFT_VALID RIGHT_VALID).
Qed.
Print Assumptions memory_affine_axis_boundary_test_evaluation.
