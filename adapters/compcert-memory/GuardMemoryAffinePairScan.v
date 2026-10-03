From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop ClightFramedLoop ClightTempFrame
  CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryBufferOffsets GuardMemoryPointerAccess
  GuardMemoryMultiPointerCells GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities
  GuardMemoryPointerCellComparison GuardMemoryBooleanScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Import GuardMemoryAffineRangeAddress.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryNaryAffineExpressions.

Lemma memory_affine_range_test_evaluation first_expression second_expression first_term second_term original_iterator
  ge locals original current memory extent first second x y i j :
  memory_encode_nary_index [original_iterator] first_expression = Some first_term ->
  memory_encode_nary_index [original_iterator] second_expression = Some second_term ->
  first <> second -> extent <= Int.max_signed+1 ->
  current ! first = original ! first -> current ! second = original ! second ->
  current ! x = Some (Vint (Int.repr i)) -> current ! y = Some (Vint (Int.repr j)) ->
  memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell first (memory_nary_index_value first_term [i])) ->
  memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell second (memory_nary_index_value second_term [j])) ->
  expression_test (memory_pointer_cells_test (memory_affine_range_address first x first_expression) (memory_affine_range_address second y second_expression))
    (Entry ge locals current memory)
    (memory_cell_pair_address_check (memory_multi_pointer_locations original extent) (point_cell first (memory_nary_index_value first_term [i])) (point_cell second (memory_nary_index_value second_term [j]))).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE DISTINCT EXTENT FIRST SECOND X Y FIRST_CAP SECOND_CAP.
  destruct (@memory_affine_range_address_binding first_expression first_term original_iterator ge locals original current memory extent first x i FIRST_ENCODE EXTENT FIRST X FIRST_CAP)
    as [left [left_offset [LEFT [LEFT_CHUNK [LEFT_OFFSET [LEFT_PURE [LEFT_TYPE [LEFT_VALUE [LEFT_VALID LEFT_ALIGN]]]]]]]]].
  destruct (@memory_affine_range_address_binding second_expression second_term original_iterator ge locals original current memory extent second y j SECOND_ENCODE EXTENT SECOND Y SECOND_CAP)
    as [right [right_offset [RIGHT [RIGHT_CHUNK [RIGHT_OFFSET [RIGHT_PURE [RIGHT_TYPE [RIGHT_VALUE [RIGHT_VALID RIGHT_ALIGN]]]]]]]]].
  unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec as [SAME|].
  - apply (f_equal arr_id) in SAME; cbn [arr_id point_cell] in SAME; contradiction.
  - rewrite LEFT,RIGHT,LEFT_OFFSET,RIGHT_OFFSET,<-memory_pointer_eq_unsigned.
    exact (@memory_pointer_cells_test_evaluation ge locals current memory _ _ _ _ _ _
      LEFT_TYPE RIGHT_TYPE LEFT_VALUE RIGHT_VALUE LEFT_VALID RIGHT_VALID).
Qed.

Definition memory_affine_range_pair_statement x y flag bound first second first_expression second_expression :=
  Ssequence (Sset x (Econst_int Int.zero type_int32s))
    (counted_loop x bound
      (Ssequence (Sset y (Econst_int Int.zero type_int32s))
        (counted_loop y bound
          (memory_boolean_test_body flag
            (memory_pointer_cells_test (memory_affine_range_address first x first_expression) (memory_affine_range_address second y second_expression)))))).

Definition memory_affine_range_pair_check locations count first second first_term second_term :=
  memory_boolean_scan_result
    (fun i => memory_boolean_scan_result
      (fun j => memory_cell_pair_address_check locations (point_cell first (memory_nary_index_value first_term [i])) (point_cell second (memory_nary_index_value second_term [j])))
      0 (Z.to_nat count)) 0 (Z.to_nat count).

Theorem memory_affine_range_pair_execution first_expression second_expression first_term second_term original_iterator
  fe ge locals original current memory extent first second x y flag bound live count accepted :
  memory_encode_nary_index [original_iterator] first_expression = Some first_term ->
  memory_encode_nary_index [original_iterator] second_expression = Some second_term ->
  first <> second -> extent <= Int.max_signed+1 -> 0 <= count -> signed_range count ->
  NoDup [x;y;flag;bound] -> ~ In x (first::second::live) -> ~ In y (first::second::live) ->
  ~ In flag (first::second::live) ->
  temp_agree (first::second::live) original current ->
  current ! bound = Some (Vint (Int.repr count)) -> current ! flag = Some (memory_boolean_word accepted) ->
  (forall index, 0 <= index < count ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell first (memory_nary_index_value first_term [index])) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell second (memory_nary_index_value second_term [index]))) ->
  exists after,
    exec_stmt fe ge locals current memory (memory_affine_range_pair_statement x y flag bound first second first_expression second_expression)
      E0 after memory Out_normal /\
    temp_agree (bound::first::second::live) current after /\
    after ! flag = Some (memory_boolean_word
      (accepted && memory_affine_range_pair_check (memory_multi_pointer_locations original extent) count first second first_term second_term)).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE DISTINCT EXTENT POS RANGE UNIQUE XFRESH YFRESH FFRESH POINTERS BOUND FLAG CAPABLE.
  inversion UNIQUE as [|xx xs NOTX UNIQUE_Y]; subst.
  inversion UNIQUE_Y as [|yy ys NOTY UNIQUE_F]; subst.
  inversion UNIQUE_F as [|ff fs NOTF UNIQUE_B]; subst.
  assert (XY : x <> y) by (intro SAME; apply NOTX; subst; cbn; auto).
  assert (XB : x <> bound) by (intro SAME; apply NOTX; subst; cbn; auto).
  assert (XF : x <> flag) by (intro SAME; apply NOTX; subst; cbn; auto).
  assert (YB : y <> bound) by (intro SAME; apply NOTY; subst; cbn; auto).
  assert (YF : y <> flag) by (intro SAME; apply NOTY; subst; cbn; auto).
  assert (BF : bound <> flag) by (intro SAME; apply NOTF; subst; cbn; auto).
  set (initialized := counter_temps x current 0).
  set (test := fun i => memory_boolean_scan_result
    (fun j => memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
      (point_cell first (memory_nary_index_value first_term [i])) (point_cell second (memory_nary_index_value second_term [j]))) 0 (Z.to_nat count)).
  assert (BODY : forall i temps good, signed_range i -> 0 <= i < count ->
    temps ! x = Some (Vint (Int.repr i)) -> temps ! bound = Some (Vint (Int.repr count)) ->
    temps ! flag = Some (memory_boolean_word good) -> temp_agree [first;second] original temps ->
    exists after,
      exec_stmt fe ge locals temps memory
        (Ssequence (Sset y (Econst_int Int.zero type_int32s))
          (counted_loop y bound (memory_boolean_test_body flag
            (memory_pointer_cells_test (memory_affine_range_address first x first_expression) (memory_affine_range_address second y second_expression)))))
        E0 after memory Out_normal /\
      temp_agree (x::bound::first::second::live) temps after /\
      after ! flag = Some (memory_boolean_word (good && test i))).
  { intros i temps good IRANGE INDEX ITER UPPER GOOD FRAME.
    set (inner := counter_temps y temps 0).
    assert (INNER_BODY : forall j inside before, signed_range j -> 0 <= j < count ->
      inside ! y = Some (Vint (Int.repr j)) -> inside ! bound = Some (Vint (Int.repr count)) ->
      inside ! flag = Some (memory_boolean_word before) ->
      temp_agree (x::first::second::live) inner inside ->
      exists after,
        exec_stmt fe ge locals inside memory (memory_boolean_test_body flag
          (memory_pointer_cells_test (memory_affine_range_address first x first_expression) (memory_affine_range_address second y second_expression)))
          E0 after memory Out_normal /\ temp_agree (y::bound::x::first::second::live) inside after /\
        after ! flag = Some (memory_boolean_word (before && memory_cell_pair_address_check
          (memory_multi_pointer_locations original extent) (point_cell first (memory_nary_index_value first_term [i])) (point_cell second (memory_nary_index_value second_term [j]))))).
    { intros j inside before JRANGE JINDEX JITER JUPPER JGOOD INNER_FRAME.
      apply memory_boolean_test_body_execution; [cbn in FFRESH |- *; intuition congruence|exact JGOOD|].
      eapply memory_affine_range_test_evaluation; [exact FIRST_ENCODE|exact SECOND_ENCODE|exact DISTINCT|exact EXTENT| | | |exact JITER| |].
      - rewrite INNER_FRAME by (cbn; auto); unfold inner,counter_temps; rewrite PTree.gso by (intro SAME; subst; apply YFRESH; cbn; auto).
        exact (FRAME first (or_introl eq_refl)).
      - rewrite INNER_FRAME by (cbn; auto); unfold inner,counter_temps; rewrite PTree.gso by (intro SAME; subst; apply YFRESH; cbn; auto).
        exact (FRAME second (or_intror (or_introl eq_refl))).
      - rewrite INNER_FRAME by (cbn; auto); unfold inner,counter_temps; rewrite PTree.gso by congruence; exact ITER.
      - exact (proj1 (CAPABLE i INDEX)).
      - exact (proj2 (CAPABLE j JINDEX)). }
    destruct (@memory_boolean_scan_loop fe ge locals memory y bound flag
      (memory_boolean_test_body flag (memory_pointer_cells_test
        (memory_affine_range_address first x first_expression) (memory_affine_range_address second y second_expression)))
      count 0 (x::first::second::live) inner
      (fun j => memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
        (point_cell first (memory_nary_index_value first_term [i])) (point_cell second (memory_nary_index_value second_term [j])))
      YB YF BF ltac:(cbn in YFRESH |- *; intuition congruence) RANGE INNER_BODY
      (Z.to_nat count) 0 inner good)
      as [after [RUN [AFTER_FRAME [AFTER_ITER AFTER_FLAG]]]].
    - rewrite Z2Nat.id by exact POS; lia.
    - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
    - lia.
    - unfold inner,counter_temps; apply PTree.gss.
    - unfold inner,counter_temps; rewrite PTree.gso by congruence; exact UPPER.
    - unfold inner,counter_temps; rewrite PTree.gso by congruence; exact GOOD.
    - apply temp_agree_refl.
    - exists after; split.
      + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor; constructor|exact RUN].
      + split; [|exact AFTER_FLAG].
        eapply temp_agree_trans with (le1 := inner).
        * unfold inner,counter_temps; apply temp_agree_set; cbn in YFRESH |- *; intuition congruence.
        * eapply temp_agree_weaken; [|exact AFTER_FRAME]; cbn; intuition. }
  assert (OUTER_BODY : forall i temps good, signed_range i -> 0 <= i < count ->
    temps ! x = Some (Vint (Int.repr i)) -> temps ! bound = Some (Vint (Int.repr count)) ->
    temps ! flag = Some (memory_boolean_word good) -> temp_agree (first::second::live) original temps ->
    exists after,
      exec_stmt fe ge locals temps memory
        (Ssequence (Sset y (Econst_int Int.zero type_int32s))
          (counted_loop y bound (memory_boolean_test_body flag
            (memory_pointer_cells_test (memory_affine_range_address first x first_expression) (memory_affine_range_address second y second_expression)))))
        E0 after memory Out_normal /\
      temp_agree (x::bound::first::second::live) temps after /\
      after ! flag = Some (memory_boolean_word (good && test i))).
  { intros i temps good IRANGE INDEX ITER UPPER GOOD FRAME; apply BODY; auto.
    eapply temp_agree_weaken; [|exact FRAME]; cbn; intuition. }
  destruct (@memory_boolean_scan_loop fe ge locals memory x bound flag
    (Ssequence (Sset y (Econst_int Int.zero type_int32s))
      (counted_loop y bound (memory_boolean_test_body flag
        (memory_pointer_cells_test (memory_affine_range_address first x first_expression) (memory_affine_range_address second y second_expression)))))
    count 0 (first::second::live) original test XB XF BF XFRESH RANGE OUTER_BODY
    (Z.to_nat count) 0 initialized accepted)
    as [after [RUN [FRAME [ITER RESULT]]]].
  - rewrite Z2Nat.id by exact POS; lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - lia.
  - unfold initialized,counter_temps; apply PTree.gss.
  - unfold initialized,counter_temps; rewrite PTree.gso by congruence; exact BOUND.
  - unfold initialized,counter_temps; rewrite PTree.gso by congruence; exact FLAG.
  - eapply temp_agree_trans; [exact POINTERS|].
    unfold initialized,counter_temps; apply temp_agree_set; exact XFRESH.
  - exists after; split.
    + unfold memory_affine_range_pair_statement; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
        [constructor; constructor|exact RUN].
    + split; [|exact RESULT].
      eapply temp_agree_trans with (le1 := initialized); [|exact FRAME].
      unfold initialized,counter_temps; apply temp_agree_set; cbn in XFRESH |- *; intuition congruence.

Qed.

Print Assumptions memory_affine_range_test_evaluation.
Print Assumptions memory_affine_range_pair_execution.
