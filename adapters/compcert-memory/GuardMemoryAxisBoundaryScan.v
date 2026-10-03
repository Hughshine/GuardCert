From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryBooleanScan GuardMemoryBooleanRectangle GuardMemoryBooleanRectangleExecution
  GuardMemoryFootprintCapabilities GuardMemoryNaryAffineExpressions GuardMemoryRecursiveSource.
From GuardMemory Require Import GuardMemoryAxisBoundaryTest GuardMemoryAxisBoundaryCells.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_axis_boundary_mask_statement layout counters zero flag bounds mask first second first_expression second_expression :=
  memory_boolean_rectangle_statement counters bounds (memory_boolean_test_body flag
    (memory_affine_axis_boundary_test layout counters zero mask first second first_expression second_expression)).

Definition memory_affine_axis_boundary_mask_check locations counts first second first_term second_term mask :=
  memory_boolean_rectangle_result
    (memory_affine_axis_boundary_coordinate_check locations first second first_term second_term mask) counts [].

Theorem memory_affine_axis_boundary_mask_execution first_expression second_expression first_term second_term
  layout counters zero bounds counts mask fe ge locals original current memory extent first second flag live accepted :
  memory_encode_nary_index layout first_expression = Some first_term ->
  memory_encode_nary_index layout second_expression = Some second_term ->
  NoDup layout -> NoDup counters -> length layout = length counts -> length counters = length counts ->
  length mask = length counts -> first <> second -> extent <= Int.max_signed+1 ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  (forall identifier, In identifier counters -> ~ In identifier (bounds++zero::first::second::live) /\ identifier <> flag) ->
  ~ In flag (bounds++zero::first::second::live) ->
  memory_nest_bindings bounds counts original ->
  temp_agree (bounds++first::second::live) original current ->
  current ! zero = Some (Vint Int.zero) -> current ! flag = Some (memory_boolean_word accepted) ->
  (forall coordinates, Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell first (memory_nary_index_value first_term coordinates)) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell second (memory_nary_index_value second_term coordinates))) ->
  exists after,
    exec_stmt fe ge locals current memory
      (memory_affine_axis_boundary_mask_statement layout counters zero flag bounds mask first second first_expression second_expression)
      E0 after memory Out_normal /\
    temp_agree (bounds++zero::first::second::live) current after /\
    after ! flag = Some (memory_boolean_word (accepted && memory_affine_axis_boundary_mask_check
      (memory_multi_pointer_locations original extent) counts first second first_term second_term mask)).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE COUNTER_UNIQUE SOURCE_LENGTH COUNTER_LENGTH MASK DISTINCT EXTENT
    RANGES FRESH FLAG_FRESH WORDS FRAME ZERO FLAG CAPS.
  assert (SIGNED : Forall signed_range counts).
  { eapply Forall_impl; [|exact RANGES]; intros count [POS RANGE]; exact RANGE. }
  assert (CURRENT_WORDS : memory_nest_bindings bounds counts current).
  { eapply memory_nest_bindings_frame_from; [|exact FRAME|exact WORDS].
    intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
  assert (BODY : forall coordinates temps good,
    Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
    memory_nest_bindings counters coordinates temps ->
    temp_agree (bounds++zero::first::second::live) current temps ->
    temps ! flag = Some (memory_boolean_word good) ->
    exists after,
      exec_stmt fe ge locals temps memory (memory_boolean_test_body flag
        (memory_affine_axis_boundary_test layout counters zero mask first second first_expression second_expression))
        E0 after memory Out_normal /\
      temp_agree (counters++bounds++zero::first::second::live) temps after /\
      after ! flag = Some (memory_boolean_word (good && memory_affine_axis_boundary_coordinate_check
        (memory_multi_pointer_locations original extent) first second first_term second_term mask coordinates))).
  { intros coordinates temps good COORDINATES COORD_WORDS PUBLIC_FRAME GOOD.
    apply memory_boolean_test_body_execution; [|exact GOOD|].
    - intro BAD; apply in_app_or in BAD as [BAD|BAD].
      + destruct (FRESH flag BAD) as [_ FALSE]; apply FALSE; reflexivity.
      + apply FLAG_FRESH; exact BAD.
    - eapply memory_affine_axis_boundary_test_evaluation with (counts := counts); try eassumption; try lia.
      + rewrite PUBLIC_FRAME by (apply in_or_app; right; cbn; auto).
        apply FRAME; apply in_or_app; right; cbn; auto.
      + rewrite PUBLIC_FRAME by (apply in_or_app; right; cbn; auto).
        apply FRAME; apply in_or_app; right; cbn; auto.
      + rewrite PUBLIC_FRAME by (apply in_or_app; right; cbn; auto); exact ZERO. }
  exact (@memory_boolean_rectangle_execution fe ge locals memory flag counters bounds counts (zero::first::second::live)
    current (memory_boolean_test_body flag
      (memory_affine_axis_boundary_test layout counters zero mask first second first_expression second_expression))
    (memory_affine_axis_boundary_coordinate_check (memory_multi_pointer_locations original extent) first second first_term second_term mask)
    COUNTER_UNIQUE FRESH FLAG_FRESH RANGES COUNTER_LENGTH CURRENT_WORDS BODY current accepted
    (temp_agree_refl _ _) FLAG).
Qed.
Print Assumptions memory_affine_axis_boundary_mask_execution.
