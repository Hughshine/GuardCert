From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryBufferOffsets
  GuardMemoryMultiPointerCells GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities
  GuardMemoryPointerCellComparison GuardMemoryBooleanScan GuardMemoryRecursiveSource
  GuardMemoryAffineSourceExpressions GuardMemoryNaryAffineExpressions.
From GuardMemory Require Import GuardMemoryAffineAxisRenaming GuardMemoryAffineAxisAddress
  GuardMemoryBooleanRectangle GuardMemoryBooleanRectangleExecution.
From GuardMemory Require Import GuardMemoryWindowCells GuardMemoryWindowAffineAxisAddress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma window_affine_axis_pair_test_evaluation first_expression second_expression first_term second_term
  layout left_counters right_counters first_coordinates second_coordinates
  ge locals original current memory lower upper first second :
  memory_encode_nary_index layout first_expression = Some first_term ->
  memory_encode_nary_index layout second_expression = Some second_term ->
  NoDup layout -> NoDup left_counters -> NoDup right_counters ->
  length layout = length left_counters -> length layout = length right_counters ->
  first <> second -> signed_range lower -> signed_range (upper-1) ->
  current ! first = original ! first -> current ! second = original ! second ->
  memory_nest_bindings left_counters first_coordinates current ->
  memory_nest_bindings right_counters second_coordinates current ->
  memory_cell_capable (window_multi_pointer_locations original lower upper) memory
    (point_cell first (memory_nary_index_value first_term first_coordinates)) ->
  memory_cell_capable (window_multi_pointer_locations original lower upper) memory
    (point_cell second (memory_nary_index_value second_term second_coordinates)) ->
  expression_test
    (memory_pointer_cells_test
      (memory_affine_axis_address first layout left_counters first_expression)
      (memory_affine_axis_address second layout right_counters second_expression))
    (Entry ge locals current memory)
    (memory_cell_pair_address_check (window_multi_pointer_locations original lower upper)
      (point_cell first (memory_nary_index_value first_term first_coordinates))
      (point_cell second (memory_nary_index_value second_term second_coordinates))).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE LEFT_UNIQUE RIGHT_UNIQUE LEFT_LENGTH RIGHT_LENGTH
    DISTINCT LOWER UPPER FIRST SECOND LEFT_WORDS RIGHT_WORDS FIRST_CAP SECOND_CAP.
  destruct (@window_affine_axis_address_binding first_expression first_term layout left_counters first_coordinates
    ge locals original current memory lower upper first FIRST_ENCODE SOURCE_UNIQUE LEFT_UNIQUE LEFT_LENGTH LOWER UPPER FIRST LEFT_WORDS FIRST_CAP)
    as [left [left_offset [LEFT [LEFT_CHUNK [LEFT_OFFSET [LEFT_PURE [LEFT_TYPE [LEFT_VALUE [LEFT_VALID LEFT_ALIGN]]]]]]]]].
  destruct (@window_affine_axis_address_binding second_expression second_term layout right_counters second_coordinates
    ge locals original current memory lower upper second SECOND_ENCODE SOURCE_UNIQUE RIGHT_UNIQUE RIGHT_LENGTH LOWER UPPER SECOND RIGHT_WORDS SECOND_CAP)
    as [right [right_offset [RIGHT [RIGHT_CHUNK [RIGHT_OFFSET [RIGHT_PURE [RIGHT_TYPE [RIGHT_VALUE [RIGHT_VALID RIGHT_ALIGN]]]]]]]]].
  unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec as [SAME|].
  - apply (f_equal arr_id) in SAME; cbn [arr_id point_cell] in SAME; contradiction.
  - rewrite LEFT,RIGHT,LEFT_OFFSET,RIGHT_OFFSET,<-memory_pointer_eq_unsigned.
    exact (@memory_pointer_cells_test_evaluation ge locals current memory _ _ _ _ _ _
      LEFT_TYPE RIGHT_TYPE LEFT_VALUE RIGHT_VALUE LEFT_VALID RIGHT_VALID).
Qed.

Print Assumptions window_affine_axis_pair_test_evaluation.
