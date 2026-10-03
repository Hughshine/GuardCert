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
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_axis_pair_check locations counts first second first_term second_term :=
  memory_boolean_rectangle_result (fun first_coordinates =>
    memory_boolean_rectangle_result (fun second_coordinates =>
      memory_cell_pair_address_check locations
        (point_cell first (memory_nary_index_value first_term first_coordinates))
        (point_cell second (memory_nary_index_value second_term second_coordinates))) counts []) counts [].

Definition memory_affine_axis_pair_statement layout left_counters right_counters flag bounds
  first second first_expression second_expression :=
  memory_boolean_rectangle_statement left_counters bounds
    (memory_boolean_rectangle_statement right_counters bounds
      (memory_boolean_test_body flag
        (memory_pointer_cells_test
          (memory_affine_axis_address first layout left_counters first_expression)
          (memory_affine_axis_address second layout right_counters second_expression)))).

Lemma memory_affine_axis_pair_test_evaluation first_expression second_expression first_term second_term
  layout left_counters right_counters first_coordinates second_coordinates
  ge locals original current memory extent first second :
  memory_encode_nary_index layout first_expression = Some first_term ->
  memory_encode_nary_index layout second_expression = Some second_term ->
  NoDup layout -> NoDup left_counters -> NoDup right_counters ->
  length layout = length left_counters -> length layout = length right_counters ->
  first <> second -> extent <= Int.max_signed+1 ->
  current ! first = original ! first -> current ! second = original ! second ->
  memory_nest_bindings left_counters first_coordinates current ->
  memory_nest_bindings right_counters second_coordinates current ->
  memory_cell_capable (memory_multi_pointer_locations original extent) memory
    (point_cell first (memory_nary_index_value first_term first_coordinates)) ->
  memory_cell_capable (memory_multi_pointer_locations original extent) memory
    (point_cell second (memory_nary_index_value second_term second_coordinates)) ->
  expression_test
    (memory_pointer_cells_test
      (memory_affine_axis_address first layout left_counters first_expression)
      (memory_affine_axis_address second layout right_counters second_expression))
    (Entry ge locals current memory)
    (memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
      (point_cell first (memory_nary_index_value first_term first_coordinates))
      (point_cell second (memory_nary_index_value second_term second_coordinates))).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE LEFT_UNIQUE RIGHT_UNIQUE LEFT_LENGTH RIGHT_LENGTH
    DISTINCT EXTENT FIRST SECOND LEFT_WORDS RIGHT_WORDS FIRST_CAP SECOND_CAP.
  destruct (@memory_affine_axis_address_binding first_expression first_term layout left_counters first_coordinates
    ge locals original current memory extent first FIRST_ENCODE SOURCE_UNIQUE LEFT_UNIQUE LEFT_LENGTH EXTENT FIRST LEFT_WORDS FIRST_CAP)
    as [left [left_offset [LEFT [LEFT_CHUNK [LEFT_OFFSET [LEFT_PURE [LEFT_TYPE [LEFT_VALUE [LEFT_VALID LEFT_ALIGN]]]]]]]]].
  destruct (@memory_affine_axis_address_binding second_expression second_term layout right_counters second_coordinates
    ge locals original current memory extent second SECOND_ENCODE SOURCE_UNIQUE RIGHT_UNIQUE RIGHT_LENGTH EXTENT SECOND RIGHT_WORDS SECOND_CAP)
    as [right [right_offset [RIGHT [RIGHT_CHUNK [RIGHT_OFFSET [RIGHT_PURE [RIGHT_TYPE [RIGHT_VALUE [RIGHT_VALID RIGHT_ALIGN]]]]]]]]].
  unfold memory_cell_pair_address_check; destruct memory_cell_identity_dec as [SAME|].
  - apply (f_equal arr_id) in SAME; cbn [arr_id point_cell] in SAME; contradiction.
  - rewrite LEFT,RIGHT,LEFT_OFFSET,RIGHT_OFFSET,<-memory_pointer_eq_unsigned.
    exact (@memory_pointer_cells_test_evaluation ge locals current memory _ _ _ _ _ _
      LEFT_TYPE RIGHT_TYPE LEFT_VALUE RIGHT_VALUE LEFT_VALID RIGHT_VALID).
Qed.

Theorem memory_affine_axis_pair_execution first_expression second_expression first_term second_term
  layout left_counters right_counters bounds counts
  fe ge locals original current memory extent first second flag live accepted :
  memory_encode_nary_index layout first_expression = Some first_term ->
  memory_encode_nary_index layout second_expression = Some second_term ->
  NoDup layout -> NoDup (left_counters++right_counters) ->
  length layout = length counts -> length left_counters = length counts -> length right_counters = length counts ->
  first <> second -> extent <= Int.max_signed+1 ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  (forall identifier, In identifier (left_counters++right_counters) ->
    ~ In identifier (bounds++first::second::live) /\ identifier <> flag) ->
  ~ In flag (bounds++first::second::live) ->
  memory_nest_bindings bounds counts original ->
  temp_agree (bounds++first::second::live) original current ->
  current ! flag = Some (memory_boolean_word accepted) ->
  (forall coordinates, Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell first (memory_nary_index_value first_term coordinates)) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell second (memory_nary_index_value second_term coordinates))) ->
  exists after,
    exec_stmt fe ge locals current memory
      (memory_affine_axis_pair_statement layout left_counters right_counters flag bounds
        first second first_expression second_expression) E0 after memory Out_normal /\
    temp_agree (bounds++first::second::live) current after /\
    after ! flag = Some (memory_boolean_word
      (accepted && memory_affine_axis_pair_check (memory_multi_pointer_locations original extent)
        counts first second first_term second_term)).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE COUNTER_UNIQUE SOURCE_LENGTH LEFT_LENGTH RIGHT_LENGTH
    DISTINCT EXTENT RANGES FRESH FLAG_FRESH WORDS FRAME FLAG CAPABLE.
  pose proof (@NoDup_app_remove_r _ left_counters right_counters COUNTER_UNIQUE) as LEFT_UNIQUE.
  pose proof (@NoDup_app_remove_l _ left_counters right_counters COUNTER_UNIQUE) as RIGHT_UNIQUE.
  assert (DISJOINT : forall identifier, In identifier left_counters -> ~ In identifier right_counters).
  { intros identifier MEMBER OTHER; apply in_split in MEMBER as [prefix [suffix SAME]].
    rewrite SAME,<-app_assoc in COUNTER_UNIQUE; cbn in COUNTER_UNIQUE.
    apply NoDup_remove_2 in COUNTER_UNIQUE; apply COUNTER_UNIQUE.
    apply in_or_app; right; apply in_or_app; right; exact OTHER. }
  set (inner_body := memory_boolean_test_body flag
    (memory_pointer_cells_test
      (memory_affine_axis_address first layout left_counters first_expression)
      (memory_affine_axis_address second layout right_counters second_expression))).
  set (outer_body := memory_boolean_rectangle_statement right_counters bounds inner_body).
  set (pair_test := fun first_coordinates second_coordinates =>
    memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
      (point_cell first (memory_nary_index_value first_term first_coordinates))
      (point_cell second (memory_nary_index_value second_term second_coordinates))).
  assert (OUTER_FRESH : forall identifier, In identifier left_counters ->
    ~ In identifier (bounds++first::second::live) /\ identifier <> flag).
  { intros identifier MEMBER; apply FRESH; apply in_or_app; left; exact MEMBER. }
  assert (OUTER_BODY : forall first_coordinates temps good,
    Forall2 (fun coordinate count => 0 <= coordinate < count) first_coordinates counts ->
    memory_nest_bindings left_counters first_coordinates temps ->
    temp_agree (bounds++first::second::live) original temps ->
    temps ! flag = Some (memory_boolean_word good) ->
    exists after,
      exec_stmt fe ge locals temps memory outer_body E0 after memory Out_normal /\
      temp_agree (left_counters++bounds++first::second::live) temps after /\
      after ! flag = Some (memory_boolean_word
        (good && memory_boolean_rectangle_result (pair_test first_coordinates) counts []))).
  { intros first_coordinates temps good FIRST_RANGE FIRST_WORDS PUBLIC_FRAME GOOD.
    assert (INNER_FRESH : forall identifier, In identifier right_counters ->
      ~ In identifier (bounds++left_counters++first::second::live) /\ identifier <> flag).
    { intros identifier MEMBER; destruct (FRESH identifier ltac:(apply in_or_app; right; exact MEMBER)) as [PUBLIC NOT_FLAG].
      split; [|exact NOT_FLAG]; intro BAD; repeat rewrite in_app_iff in BAD; destruct BAD as [BAD|[BAD|BAD]].
      - apply PUBLIC; apply in_or_app; left; exact BAD.
      - exact (DISJOINT identifier BAD MEMBER).
      - apply PUBLIC; apply in_or_app; right; exact BAD. }
    assert (INNER_FLAG : ~ In flag (bounds++left_counters++first::second::live)).
    { intro BAD; repeat rewrite in_app_iff in BAD; destruct BAD as [BAD|[BAD|BAD]].
      - apply FLAG_FRESH; apply in_or_app; left; exact BAD.
      - destruct (OUTER_FRESH flag BAD) as [_ FALSE]; apply FALSE; reflexivity.
      - apply FLAG_FRESH; apply in_or_app; right; exact BAD. }
    assert (INNER_WORDS : memory_nest_bindings bounds counts temps).
    { eapply memory_nest_bindings_frame_from; [|exact PUBLIC_FRAME|exact WORDS].
      intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
    assert (INNER_BODY : forall second_coordinates inside before,
      Forall2 (fun coordinate count => 0 <= coordinate < count) second_coordinates counts ->
      memory_nest_bindings right_counters second_coordinates inside ->
      temp_agree (bounds++left_counters++first::second::live) temps inside ->
      inside ! flag = Some (memory_boolean_word before) ->
      exists after,
        exec_stmt fe ge locals inside memory inner_body E0 after memory Out_normal /\
        temp_agree (right_counters++bounds++left_counters++first::second::live) inside after /\
        after ! flag = Some (memory_boolean_word (before && pair_test first_coordinates second_coordinates))).
    { intros second_coordinates inside before SECOND_RANGE SECOND_WORDS INNER_FRAME BEFORE.
      unfold inner_body; apply memory_boolean_test_body_execution; [|exact BEFORE|].
      - intro BAD; repeat rewrite in_app_iff in BAD.
        destruct BAD as [BAD|[BAD|[BAD|BAD]]].
        + destruct (FRESH flag ltac:(apply in_or_app; right; exact BAD)) as [_ FALSE]; apply FALSE; reflexivity.
        + apply INNER_FLAG; apply in_or_app; left; exact BAD.
        + apply INNER_FLAG; apply in_or_app; right; apply in_or_app; left; exact BAD.
        + apply INNER_FLAG; apply in_or_app; right; apply in_or_app; right; exact BAD.
      - unfold pair_test; eapply memory_affine_axis_pair_test_evaluation;
          [exact FIRST_ENCODE|exact SECOND_ENCODE|exact SOURCE_UNIQUE|exact LEFT_UNIQUE|exact RIGHT_UNIQUE|
           lia|lia|exact DISTINCT|exact EXTENT| | | |exact SECOND_WORDS| |].
        + rewrite INNER_FRAME by (repeat rewrite in_app_iff; cbn; tauto).
          apply PUBLIC_FRAME; apply in_or_app; right; cbn; auto.
        + rewrite INNER_FRAME by (repeat rewrite in_app_iff; cbn; tauto).
          apply PUBLIC_FRAME; apply in_or_app; right; cbn; auto.
        + eapply memory_nest_bindings_frame_from; [|exact INNER_FRAME|exact FIRST_WORDS].
          intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
        + exact (proj1 (CAPABLE first_coordinates FIRST_RANGE)).
        + exact (proj2 (CAPABLE second_coordinates SECOND_RANGE)). }
    destruct (@memory_boolean_rectangle_execution fe ge locals memory flag right_counters bounds counts
      (left_counters++first::second::live) temps inner_body (pair_test first_coordinates)
      RIGHT_UNIQUE INNER_FRESH INNER_FLAG RANGES RIGHT_LENGTH INNER_WORDS INNER_BODY
      temps good ltac:(apply temp_agree_refl) GOOD) as [after [RUN [AFTER_FRAME RESULT]]].
    exists after; split; [exact RUN|split; [|exact RESULT]].
    eapply temp_agree_weaken; [|exact AFTER_FRAME];
      intros identifier MEMBER; repeat rewrite in_app_iff in *; intuition. }
  exact (@memory_boolean_rectangle_execution fe ge locals memory flag left_counters bounds counts
    (first::second::live) original outer_body
    (fun first_coordinates => memory_boolean_rectangle_result (pair_test first_coordinates) counts [])
    LEFT_UNIQUE OUTER_FRESH FLAG_FRESH RANGES LEFT_LENGTH WORDS OUTER_BODY current accepted FRAME FLAG).
Qed.
Print Assumptions memory_affine_axis_pair_execution.
