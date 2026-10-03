From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryBooleanScan GuardMemoryFootprintCapabilities GuardMemoryNaryAffineExpressions GuardMemoryRecursiveSource
  GuardMemoryAffineAxisPairScan.
From GuardMemory Require Import GuardMemoryAxisBoundaryPair.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_axis_pair_choice_statement layout left_counters right_counters flag bounds
  first second (first_term second_term : constraint) first_expression second_expression :=
  match right_counters with
  | [] => memory_affine_axis_pair_statement layout left_counters right_counters flag bounds
      first second first_expression second_expression
  | zero::_ => if List.list_eq_dec Z.eq_dec (fst first_term) (fst second_term) then
      memory_affine_axis_boundary_pair_statement layout left_counters zero flag bounds
        first second first_expression second_expression
    else memory_affine_axis_pair_statement layout left_counters right_counters flag bounds
      first second first_expression second_expression end.

Theorem memory_affine_axis_pair_choice_execution first_expression second_expression first_term second_term
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
      (memory_affine_axis_pair_choice_statement layout left_counters right_counters flag bounds
        first second first_term second_term first_expression second_expression) E0 after memory Out_normal /\
    temp_agree (bounds++first::second::live) current after /\
    after ! flag = Some (memory_boolean_word
      (accepted && memory_affine_axis_pair_check (memory_multi_pointer_locations original extent)
        counts first second first_term second_term)).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE COUNTER_UNIQUE SOURCE_LENGTH LEFT_LENGTH RIGHT_LENGTH
    DISTINCT EXTENT RANGES FRESH FLAG_FRESH WORDS FRAME FLAG CAPS.
  unfold memory_affine_axis_pair_choice_statement.
  destruct right_counters as [|zero right_counters].
  - eapply memory_affine_axis_pair_execution; eassumption.
  - destruct (List.list_eq_dec Z.eq_dec (fst first_term) (fst second_term)) as [SAME|DIFFERENT].
    + assert (ZERO_LEFT : ~ In zero left_counters).
      { intro MEMBER; apply in_split in MEMBER as [prefix [suffix LAYOUT]].
        rewrite LAYOUT,<-app_assoc in COUNTER_UNIQUE; cbn in COUNTER_UNIQUE.
        apply NoDup_remove_2 in COUNTER_UNIQUE; apply COUNTER_UNIQUE.
        apply in_or_app; right; apply in_or_app; right; cbn; auto. }
      destruct (FRESH zero ltac:(apply in_or_app; right; cbn; auto)) as [ZERO_PUBLIC ZERO_FLAG].
      eapply memory_affine_axis_boundary_pair_execution; try eassumption.
      * exact (@NoDup_app_remove_r _ left_counters (zero::right_counters) COUNTER_UNIQUE).
      * intros identifier MEMBER; apply FRESH; apply in_or_app; left; exact MEMBER.
    + eapply memory_affine_axis_pair_execution; eassumption.
Qed.
Print Assumptions memory_affine_axis_pair_choice_execution.
