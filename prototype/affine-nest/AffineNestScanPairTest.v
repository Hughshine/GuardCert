From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition
  GuardMemoryFootprintCapabilities GuardMemoryPointerCellComparison GuardMemoryWindowCells GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestScanAddress.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem affine_scan_pair_test first second first_expression second_expression left right first_value second_value
  ge locals original current memory lower upper :
  first<>second -> signed_range lower -> signed_range(upper-1) ->
  current!first=original!first -> current!second=original!second ->
  (forall identifier, In identifier(memory_source_affine_reads first_expression) ->
    current!(left identifier)=Some(Vint(Int.repr(first_value identifier)))) ->
  (forall identifier, In identifier(memory_source_affine_reads second_expression) ->
    current!(right identifier)=Some(Vint(Int.repr(second_value identifier)))) ->
  memory_cell_capable(window_multi_pointer_locations original lower upper) memory
    (point_cell first(memory_source_affine_math first_value first_expression)) ->
  memory_cell_capable(window_multi_pointer_locations original lower upper) memory
    (point_cell second(memory_source_affine_math second_value second_expression)) ->
  expression_test(memory_pointer_cells_test(affine_scan_address first left first_expression)
    (affine_scan_address second right second_expression))(Entry ge locals current memory)
    (memory_cell_pair_address_check(window_multi_pointer_locations original lower upper)
      (point_cell first(memory_source_affine_math first_value first_expression))
      (point_cell second(memory_source_affine_math second_value second_expression))).
Proof.
  intros DISTINCT LOWER UPPER FIRST SECOND LEFT_WORDS RIGHT_WORDS FIRST_CAP SECOND_CAP.
  destruct(@affine_scan_address_binding first_expression left first_value ge locals original current memory lower upper first
    LOWER UPPER FIRST LEFT_WORDS FIRST_CAP)
    as [left_location [left_offset [LEFT [LEFT_CHUNK [LEFT_OFFSET [LEFT_PURE [LEFT_TYPE [LEFT_VALUE LEFT_CAPABLE]]]]]]]].
  destruct(@affine_scan_address_binding second_expression right second_value ge locals original current memory lower upper second
    LOWER UPPER SECOND RIGHT_WORDS SECOND_CAP)
    as [right_location [right_offset [RIGHT [RIGHT_CHUNK [RIGHT_OFFSET [RIGHT_PURE [RIGHT_TYPE [RIGHT_VALUE RIGHT_CAPABLE]]]]]]]].
  unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec as [SAME|].
  - apply(f_equal arr_id) in SAME; cbn [arr_id point_cell] in SAME; contradiction.
  - rewrite LEFT,RIGHT,LEFT_OFFSET,RIGHT_OFFSET,<-memory_pointer_eq_unsigned.
    eapply memory_pointer_cells_test_evaluation; eassumption || exact(proj1 LEFT_CAPABLE) || exact(proj1 RIGHT_CAPABLE).
Qed.
Print Assumptions affine_scan_pair_test.
