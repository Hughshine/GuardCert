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
  GuardMemoryAffineAxisPairScan
  GuardMemoryBooleanRectangle GuardMemoryBooleanRectangleExecution.
From GuardMemory Require Import GuardMemoryStartedBooleanRectangle GuardMemoryStartedBooleanWrapper GuardMemoryStartedBooleanPublic.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_started_param_affine_axis_pair_check locations counts start parameter_values first second first_term second_term :=
  memory_boolean_started_all_result (fun first_coordinates =>
    memory_boolean_started_all_result (fun second_coordinates =>
      memory_cell_pair_address_check locations
        (point_cell first (memory_nary_index_value first_term (first_coordinates++parameter_values)))
        (point_cell second (memory_nary_index_value second_term (second_coordinates++parameter_values)))) counts start) counts start.

Definition memory_started_param_affine_axis_pair_statement root layout left_counters right_counters parameters flag bounds
  first second first_expression second_expression :=
  memory_boolean_started_rectangle_statement root left_counters bounds
    (memory_boolean_started_rectangle_statement root right_counters bounds
      (memory_boolean_test_body flag
        (memory_pointer_cells_test
          (memory_affine_axis_address first layout (left_counters++parameters) first_expression)
          (memory_affine_axis_address second layout (right_counters++parameters) second_expression)))).

Theorem memory_started_param_affine_axis_pair_execution first_expression second_expression first_term second_term
  root layout left_counters right_counters parameters bounds counts start parameter_values
  fe ge locals original current memory extent first second flag live accepted :
  counts <> [] -> In root live -> 0 <= start <= hd 0 counts -> signed_range start ->
  original ! root = Some (Vint (Int.repr start)) ->
  memory_encode_nary_index layout first_expression = Some first_term ->
  memory_encode_nary_index layout second_expression = Some second_term ->
  NoDup layout -> NoDup (left_counters++right_counters) ->
  NoDup (left_counters++parameters) -> NoDup (right_counters++parameters) ->
  (forall identifier, In identifier parameters -> In identifier (bounds++first::second::live)) ->
  length layout = (length counts + length parameter_values)%nat -> length left_counters = length counts -> length right_counters = length counts ->
  first <> second -> extent <= Int.max_signed+1 ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  (forall identifier, In identifier (left_counters++right_counters) ->
    ~ In identifier (bounds++first::second::live) /\ identifier <> flag) ->
  ~ In flag (bounds++first::second::live) ->
  memory_nest_bindings bounds counts original ->
  memory_nest_bindings parameters parameter_values original ->
  temp_agree (bounds++first::second::live) original current ->
  current ! flag = Some (memory_boolean_word accepted) ->
  (forall coordinates, memory_started_axis_coordinates start counts coordinates ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell first (memory_nary_index_value first_term (coordinates++parameter_values))) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell second (memory_nary_index_value second_term (coordinates++parameter_values)))) ->
  exists after,
    exec_stmt fe ge locals current memory
      (memory_started_param_affine_axis_pair_statement root layout left_counters right_counters parameters flag bounds
        first second first_expression second_expression) E0 after memory Out_normal /\
    temp_agree (bounds++first::second::live) current after /\
    after ! flag = Some (memory_boolean_word
      (accepted && memory_started_param_affine_axis_pair_check (memory_multi_pointer_locations original extent)
        counts start parameter_values first second first_term second_term)).
Proof.
  intros NONEMPTY ROOT_PUBLIC START START_RANGE ROOT_WORD FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE COUNTER_UNIQUE LEFT_FULL_UNIQUE RIGHT_FULL_UNIQUE PARAM_PUBLIC SOURCE_LENGTH LEFT_LENGTH RIGHT_LENGTH
    DISTINCT EXTENT RANGES FRESH FLAG_FRESH WORDS PARAM_WORDS FRAME FLAG CAPABLE.
  assert (LEFT_NONEMPTY : left_counters <> []).
  { intro EMPTY; rewrite EMPTY in LEFT_LENGTH; destruct counts; [contradiction|discriminate LEFT_LENGTH]. }
  assert (RIGHT_NONEMPTY : right_counters <> []).
  { intro EMPTY; rewrite EMPTY in RIGHT_LENGTH; destruct counts; [contradiction|discriminate RIGHT_LENGTH]. }
  pose proof (@NoDup_app_remove_r _ left_counters right_counters COUNTER_UNIQUE) as LEFT_UNIQUE.
  pose proof (@NoDup_app_remove_l _ left_counters right_counters COUNTER_UNIQUE) as RIGHT_UNIQUE.
  assert (DISJOINT : forall identifier, In identifier left_counters -> ~ In identifier right_counters).
  { intros identifier MEMBER OTHER; apply in_split in MEMBER as [prefix [suffix SAME]].
    rewrite SAME,<-app_assoc in COUNTER_UNIQUE; cbn in COUNTER_UNIQUE.
    apply NoDup_remove_2 in COUNTER_UNIQUE; apply COUNTER_UNIQUE.
    apply in_or_app; right; apply in_or_app; right; exact OTHER. }
  set (inner_body := memory_boolean_test_body flag
    (memory_pointer_cells_test
      (memory_affine_axis_address first layout (left_counters++parameters) first_expression)
      (memory_affine_axis_address second layout (right_counters++parameters) second_expression))).
  set (outer_body := memory_boolean_started_rectangle_statement root right_counters bounds inner_body).
  set (pair_test := fun first_coordinates second_coordinates =>
    memory_cell_pair_address_check (memory_multi_pointer_locations original extent)
      (point_cell first (memory_nary_index_value first_term (first_coordinates++parameter_values)))
      (point_cell second (memory_nary_index_value second_term (second_coordinates++parameter_values)))).
  assert (OUTER_FRESH : forall identifier, In identifier left_counters ->
    ~ In identifier (bounds++first::second::live) /\ identifier <> flag).
  { intros identifier MEMBER; apply FRESH; apply in_or_app; left; exact MEMBER. }
  assert (OUTER_BODY : forall first_coordinates temps good,
    memory_started_axis_coordinates start counts first_coordinates ->
    memory_nest_bindings left_counters first_coordinates temps ->
    temp_agree (bounds++first::second::live) original temps ->
    temps ! flag = Some (memory_boolean_word good) ->
    exists after,
      exec_stmt fe ge locals temps memory outer_body E0 after memory Out_normal /\
      temp_agree (left_counters++bounds++first::second::live) temps after /\
      after ! flag = Some (memory_boolean_word
        (good && memory_boolean_started_all_result (pair_test first_coordinates) counts start))).
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
      memory_started_axis_coordinates start counts second_coordinates ->
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
      - unfold pair_test; eapply memory_affine_axis_pair_test_evaluation
          with (left_counters := left_counters++parameters) (right_counters := right_counters++parameters)
               (first_coordinates := first_coordinates++parameter_values)
               (second_coordinates := second_coordinates++parameter_values);
          [exact FIRST_ENCODE|exact SECOND_ENCODE|exact SOURCE_UNIQUE|exact LEFT_FULL_UNIQUE|exact RIGHT_FULL_UNIQUE|
           rewrite length_app,SOURCE_LENGTH,LEFT_LENGTH;
             pose proof (@Forall2_length _ _ _ _ _ PARAM_WORDS) as PARAM_LENGTH; exact (f_equal (fun n => (length counts+n)%nat) (eq_sym PARAM_LENGTH))|
           rewrite length_app,SOURCE_LENGTH,RIGHT_LENGTH;
             pose proof (@Forall2_length _ _ _ _ _ PARAM_WORDS) as PARAM_LENGTH; exact (f_equal (fun n => (length counts+n)%nat) (eq_sym PARAM_LENGTH))|
           exact DISTINCT|exact EXTENT| | | | | |].
        + rewrite INNER_FRAME by (repeat rewrite in_app_iff; cbn; tauto).
          apply PUBLIC_FRAME; apply in_or_app; right; cbn; auto.
        + rewrite INNER_FRAME by (repeat rewrite in_app_iff; cbn; tauto).
          apply PUBLIC_FRAME; apply in_or_app; right; cbn; auto.
        + apply memory_nest_bindings_append.
          * eapply memory_nest_bindings_frame_from; [|exact INNER_FRAME|exact FIRST_WORDS].
            intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
          * eapply memory_nest_bindings_frame_from; [| |exact PARAM_WORDS].
            -- exact PARAM_PUBLIC.
            -- eapply temp_agree_trans; [exact PUBLIC_FRAME|].
               eapply temp_agree_weaken; [|exact INNER_FRAME].
               intros identifier MEMBER; repeat rewrite in_app_iff in *; intuition.
        + apply memory_nest_bindings_append; [exact SECOND_WORDS|].
          eapply memory_nest_bindings_frame_from; [exact PARAM_PUBLIC| |exact PARAM_WORDS].
          eapply temp_agree_trans; [exact PUBLIC_FRAME|].
          eapply temp_agree_weaken; [|exact INNER_FRAME].
          intros identifier MEMBER; repeat rewrite in_app_iff in *; intuition.
        + exact (proj1 (CAPABLE first_coordinates FIRST_RANGE)).
        + exact (proj2 (CAPABLE second_coordinates SECOND_RANGE)). }
    destruct (@memory_boolean_started_public_execution fe ge locals memory flag root right_counters bounds counts start
      (left_counters++first::second::live) temps inner_body (pair_test first_coordinates)
      RIGHT_NONEMPTY ltac:(apply in_or_app; right; cbn; auto) START START_RANGE
      ltac:(rewrite PUBLIC_FRAME by (apply in_or_app; right; cbn; auto); exact ROOT_WORD) RIGHT_UNIQUE INNER_FRESH INNER_FLAG RANGES RIGHT_LENGTH INNER_WORDS INNER_BODY
      temps good ltac:(apply temp_agree_refl) GOOD) as [after [RUN [AFTER_FRAME RESULT]]].
    exists after; split; [exact RUN|split; [|exact RESULT]].
    eapply temp_agree_weaken; [|exact AFTER_FRAME];
      intros identifier MEMBER; repeat rewrite in_app_iff in *; intuition. }
  exact (@memory_boolean_started_public_execution fe ge locals memory flag root left_counters bounds counts start
    (first::second::live) original outer_body
    (fun first_coordinates => memory_boolean_started_all_result (pair_test first_coordinates) counts start)
    LEFT_NONEMPTY ltac:(cbn; auto) START START_RANGE ROOT_WORD LEFT_UNIQUE OUTER_FRESH FLAG_FRESH RANGES LEFT_LENGTH WORDS OUTER_BODY current accepted FRAME FLAG).
Qed.
Print Assumptions memory_started_param_affine_axis_pair_execution.
