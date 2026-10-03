From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop ClightFramedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities GuardMemoryPointerCellComparison
  GuardMemoryNaryAffineExpressions GuardMemoryBooleanScan GuardMemoryAffineRangeAddress GuardMemoryAffinePairScan.
From GuardMemory Require Import GuardMemoryAffineEndpointCells.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_endpoint_body x y flag first second first_expression second_expression :=
  Ssequence
    (memory_boolean_test_body flag (memory_pointer_cells_test
      (memory_affine_range_address first y first_expression) (memory_affine_range_address second x second_expression)))
    (memory_boolean_test_body flag (memory_pointer_cells_test
      (memory_affine_range_address first x first_expression) (memory_affine_range_address second y second_expression))).

Theorem memory_affine_endpoint_body_execution first_expression second_expression first_term second_term original_iterator
  fe ge locals original current memory extent first second x y flag live index accepted :
  memory_encode_nary_index [original_iterator] first_expression = Some first_term ->
  memory_encode_nary_index [original_iterator] second_expression = Some second_term ->
  first <> second -> extent <= Int.max_signed+1 ->
  ~ In flag (x::y::first::second::live) -> temp_agree [first;second] original current ->
  current ! x = Some (Vint (Int.repr index)) -> current ! y = Some (Vint Int.zero) ->
  current ! flag = Some (memory_boolean_word accepted) ->
  memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell first (memory_nary_index_value first_term [0])) ->
  memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell second (memory_nary_index_value second_term [0])) ->
  memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell first (memory_nary_index_value first_term [index])) ->
  memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell second (memory_nary_index_value second_term [index])) ->
  exists after,
    exec_stmt fe ge locals current memory (memory_affine_endpoint_body x y flag first second first_expression second_expression)
      E0 after memory Out_normal /\ temp_agree (x::y::first::second::live) current after /\
    after ! flag = Some (memory_boolean_word (accepted &&
      (memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
        (point_cell first (memory_nary_index_value first_term [0])) (point_cell second (memory_nary_index_value second_term [index])) &&
       memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
        (point_cell first (memory_nary_index_value first_term [index])) (point_cell second (memory_nary_index_value second_term [0]))))).
Proof.
  intros FIRST SECOND DISTINCT EXTENT FRESH POINTERS X Y FLAG FIRST_ZERO SECOND_ZERO FIRST_INDEX SECOND_INDEX.
  destruct (@memory_boolean_test_body_execution fe ge locals current memory flag
    (memory_pointer_cells_test (memory_affine_range_address first y first_expression) (memory_affine_range_address second x second_expression))
    accepted (memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
      (point_cell first (memory_nary_index_value first_term [0])) (point_cell second (memory_nary_index_value second_term [index])))
    (x::y::first::second::live) FRESH FLAG)
    as [middle [FIRST_RUN [FIRST_FRAME FIRST_FLAG]]].
  - eapply memory_affine_range_test_evaluation; [exact FIRST|exact SECOND|exact DISTINCT|exact EXTENT| | |exact Y|exact X|exact FIRST_ZERO|exact SECOND_INDEX].
    + exact (POINTERS first ltac:(cbn; auto)).
    + exact (POINTERS second ltac:(cbn; auto)).
  - destruct (@memory_boolean_test_body_execution fe ge locals middle memory flag
      (memory_pointer_cells_test (memory_affine_range_address first x first_expression) (memory_affine_range_address second y second_expression))
      (accepted && memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
        (point_cell first (memory_nary_index_value first_term [0])) (point_cell second (memory_nary_index_value second_term [index])))
      (memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
        (point_cell first (memory_nary_index_value first_term [index])) (point_cell second (memory_nary_index_value second_term [0])))
      (x::y::first::second::live) FRESH FIRST_FLAG)
      as [after [SECOND_RUN [SECOND_FRAME SECOND_FLAG]]].
    + eapply memory_affine_range_test_evaluation; [exact FIRST|exact SECOND|exact DISTINCT|exact EXTENT| | | | |exact FIRST_INDEX|exact SECOND_ZERO].
      * rewrite FIRST_FRAME by (cbn; auto); exact (POINTERS first ltac:(cbn; auto)).
      * rewrite FIRST_FRAME by (cbn; auto); exact (POINTERS second ltac:(cbn; auto)).
      * rewrite FIRST_FRAME by (cbn; auto); exact X.
      * rewrite FIRST_FRAME by (cbn; auto); exact Y.
    + exists after; split.
      * unfold memory_affine_endpoint_body; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); eassumption.
      * split; [eapply temp_agree_trans; eassumption|rewrite andb_assoc; exact SECOND_FLAG].
Qed.
Print Assumptions memory_affine_endpoint_body_execution.

Definition memory_affine_endpoint_pair_statement x y flag bound first second first_expression second_expression :=
  Ssequence (Sset y (Econst_int Int.zero type_int32s))
    (Ssequence (Sset x (Econst_int Int.zero type_int32s))
      (counted_loop x bound (memory_affine_endpoint_body x y flag first second first_expression second_expression))).

Theorem memory_affine_endpoint_pair_execution first_expression second_expression first_term second_term original_iterator
  fe ge locals original current memory extent first second x y flag bound live count accepted :
  memory_encode_nary_index [original_iterator] first_expression = Some first_term ->
  memory_encode_nary_index [original_iterator] second_expression = Some second_term ->
  first <> second -> extent <= Int.max_signed+1 -> 0 <= count -> signed_range count ->
  NoDup [x;y;flag;bound] -> ~ In x (first::second::live) -> ~ In y (first::second::live) -> ~ In flag (first::second::live) ->
  temp_agree (first::second::live) original current ->
  current ! bound = Some (Vint (Int.repr count)) -> current ! flag = Some (memory_boolean_word accepted) ->
  (forall index, 0 <= index < count ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell first (memory_nary_index_value first_term [index])) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory (point_cell second (memory_nary_index_value second_term [index]))) ->
  exists after,
    exec_stmt fe ge locals current memory (memory_affine_endpoint_pair_statement x y flag bound first second first_expression second_expression)
      E0 after memory Out_normal /\ temp_agree (bound::first::second::live) current after /\
    after ! flag = Some (memory_boolean_word (accepted &&
      memory_affine_endpoint_pair_check (memory_multi_pointer_locations original extent) count first second first_term second_term)).
Proof.
  intros FIRST SECOND DIFFERENT EXTENT POS RANGE UNIQUE XFRESH YFRESH FFRESH POINTERS BOUND FLAG CAPS.
  assert (NAMES : x<>y /\ x<>flag /\ x<>bound /\ y<>flag /\ y<>bound /\ flag<>bound).
  { repeat rewrite NoDup_cons_iff in UNIQUE; cbn in UNIQUE; intuition congruence. }
  destruct NAMES as [XY [XF [XB [YF [YB FB]]]]].
  set (zeroed := counter_temps y current 0); set (initialized := counter_temps x zeroed 0).
  assert (SOURCE : temp_agree [first;second] original zeroed).
  { eapply temp_agree_trans; [eapply temp_agree_weaken; [|exact POINTERS]; cbn; intuition|].
    unfold zeroed,counter_temps; apply temp_agree_set; cbn in YFRESH |- *; intuition. }
  assert (BODY : forall index temps good, signed_range index -> 0 <= index < count ->
    temps ! x = Some (Vint (Int.repr index)) -> temps ! bound = Some (Vint (Int.repr count)) ->
    temps ! flag = Some (memory_boolean_word good) -> temp_agree (y::first::second::live) zeroed temps ->
    exists after,
      exec_stmt fe ge locals temps memory (memory_affine_endpoint_body x y flag first second first_expression second_expression)
        E0 after memory Out_normal /\ temp_agree (x::bound::y::first::second::live) temps after /\
      after ! flag = Some (memory_boolean_word (good &&
        (memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
          (point_cell first (memory_nary_index_value first_term [0])) (point_cell second (memory_nary_index_value second_term [index])) &&
         memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
          (point_cell first (memory_nary_index_value first_term [index])) (point_cell second (memory_nary_index_value second_term [0])))))).
  { intros index temps good IRANGE INDEX ITER UPPER GOOD FRAME.
    assert (ZERO : 0<=0<count) by lia.
    destruct (@memory_affine_endpoint_body_execution first_expression second_expression first_term second_term original_iterator
      fe ge locals original temps memory extent first second x y flag (bound::live) index good
      FIRST SECOND DIFFERENT EXTENT) as [after [RUN [AGREE RESULT]]].
    - cbn in FFRESH |- *; intuition congruence.
    - eapply temp_agree_trans; [exact SOURCE|eapply temp_agree_weaken; [|exact FRAME]; cbn; intuition].
    - exact ITER.
    - rewrite FRAME by (cbn; auto); unfold zeroed,counter_temps; apply PTree.gss.
    - exact GOOD.
    - exact (proj1 (CAPS 0 ZERO)).
    - exact (proj2 (CAPS 0 ZERO)).
    - exact (proj1 (CAPS index INDEX)).
    - exact (proj2 (CAPS index INDEX)).
    - exists after; split; [exact RUN|split; [eapply temp_agree_weaken; [|exact AGREE]; cbn; intuition|exact RESULT]]. }
  destruct (@memory_boolean_scan_loop fe ge locals memory x bound flag
    (memory_affine_endpoint_body x y flag first second first_expression second_expression)
    count 0 (y::first::second::live) zeroed
    (fun index => memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
      (point_cell first (memory_nary_index_value first_term [0])) (point_cell second (memory_nary_index_value second_term [index])) &&
      memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
      (point_cell first (memory_nary_index_value first_term [index])) (point_cell second (memory_nary_index_value second_term [0])))
    XB XF ltac:(congruence) ltac:(cbn in XFRESH |- *; intuition congruence) RANGE BODY
    (Z.to_nat count) 0 initialized accepted) as [after [RUN [FRAME [EXIT RESULT]]]].
  - rewrite Z2Nat.id by exact POS; lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - lia.
  - unfold initialized,counter_temps; apply PTree.gss.
  - unfold initialized,zeroed,counter_temps; rewrite !PTree.gso by congruence; exact BOUND.
  - unfold initialized,zeroed,counter_temps; rewrite !PTree.gso by congruence; exact FLAG.
  - unfold initialized,counter_temps; apply temp_agree_set; cbn in XFRESH |- *; intuition congruence.
  - exists after; split.
    + unfold memory_affine_endpoint_pair_statement.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|exact RUN].
    + split; [|exact RESULT].
      eapply temp_agree_trans with (le1:=zeroed).
      * unfold zeroed,counter_temps; apply temp_agree_set; cbn in YFRESH |- *; intuition congruence.
      * eapply temp_agree_trans with (le1:=initialized).
        -- unfold initialized,counter_temps; apply temp_agree_set; cbn in XFRESH |- *; intuition congruence.
        -- eapply temp_agree_weaken; [|exact FRAME]; cbn; intuition.
Qed.
Print Assumptions memory_affine_endpoint_pair_execution.
