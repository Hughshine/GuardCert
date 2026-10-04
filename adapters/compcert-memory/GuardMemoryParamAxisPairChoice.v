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
From GuardMemory Require Import GuardMemoryParamAxisPairScan.
From GuardMemory Require Import GuardMemoryParamBoundaryPair.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_param_affine_axis_pair_choice_statement layout left_counters right_counters parameters flag bounds
  first second (first_term second_term : constraint) first_expression second_expression :=
  match right_counters with
  | [] => memory_param_affine_axis_pair_statement layout left_counters right_counters parameters flag bounds
      first second first_expression second_expression
  | zero::_ => if List.list_eq_dec Z.eq_dec (resize (length left_counters) (fst first_term)) (resize (length left_counters) (fst second_term)) then
      memory_param_affine_axis_boundary_pair_statement layout left_counters parameters zero flag bounds
        first second first_expression second_expression
    else memory_param_affine_axis_pair_statement layout left_counters right_counters parameters flag bounds
      first second first_expression second_expression end.

Theorem memory_param_affine_axis_pair_choice_execution first_expression second_expression first_term second_term
  layout left_counters right_counters parameters bounds counts parameter_values
  fe ge locals original current memory extent first second flag live accepted :
  memory_encode_nary_index layout first_expression = Some first_term ->
  memory_encode_nary_index layout second_expression = Some second_term ->
  NoDup layout -> NoDup (left_counters++right_counters) ->
  NoDup (left_counters++parameters) -> NoDup (right_counters++parameters) ->
  (forall identifier, In identifier parameters -> In identifier (bounds++first::second::live)) ->
  length layout = (length counts+length parameter_values)%nat -> length left_counters = length counts -> length right_counters = length counts ->
  first <> second -> extent <= Int.max_signed+1 ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  (forall identifier, In identifier (left_counters++right_counters) ->
    ~ In identifier (bounds++first::second::live) /\ identifier <> flag) ->
  ~ In flag (bounds++first::second::live) ->
  memory_nest_bindings bounds counts original ->
  memory_nest_bindings parameters parameter_values original -> Forall signed_range parameter_values ->
  temp_agree (bounds++first::second::live) original current ->
  current ! flag = Some (memory_boolean_word accepted) ->
  (forall coordinates, Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell first (memory_nary_index_value first_term (coordinates++parameter_values))) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell second (memory_nary_index_value second_term (coordinates++parameter_values)))) ->
  exists after,
    exec_stmt fe ge locals current memory
      (memory_param_affine_axis_pair_choice_statement layout left_counters right_counters parameters flag bounds
        first second first_term second_term first_expression second_expression) E0 after memory Out_normal /\
    temp_agree (bounds++first::second::live) current after /\
    after ! flag = Some (memory_boolean_word
      (accepted && memory_param_affine_axis_pair_check (memory_multi_pointer_locations original extent)
        counts parameter_values first second first_term second_term)).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE COUNTER_UNIQUE LEFT_FULL_UNIQUE RIGHT_FULL_UNIQUE PARAM_PUBLIC SOURCE_LENGTH LEFT_LENGTH RIGHT_LENGTH
    DISTINCT EXTENT RANGES FRESH FLAG_FRESH WORDS PARAM_WORDS PARAM_SIGNED FRAME FLAG CAPS.
  unfold memory_param_affine_axis_pair_choice_statement.
  destruct right_counters as [|zero right_counters].
  - eapply memory_param_affine_axis_pair_execution; eassumption.
  - destruct (List.list_eq_dec Z.eq_dec (resize (length left_counters) (fst first_term)) (resize (length left_counters) (fst second_term))) as [SAME|DIFFERENT].
    + rewrite LEFT_LENGTH in SAME.
      assert (ZERO_LEFT : ~ In zero left_counters).
      { intro MEMBER; apply in_split in MEMBER as [prefix [suffix LAYOUT]].
        rewrite LAYOUT,<-app_assoc in COUNTER_UNIQUE; cbn in COUNTER_UNIQUE.
        apply NoDup_remove_2 in COUNTER_UNIQUE; apply COUNTER_UNIQUE.
        apply in_or_app; right; apply in_or_app; right; cbn; auto. }
      destruct (FRESH zero ltac:(apply in_or_app; right; cbn; auto)) as [ZERO_PUBLIC ZERO_FLAG].
      eapply memory_param_affine_axis_boundary_pair_execution; try eassumption.
      * exact (@NoDup_app_remove_r _ left_counters (zero::right_counters) COUNTER_UNIQUE).
      * intros identifier MEMBER; apply FRESH; apply in_or_app; left; exact MEMBER.
    + eapply memory_param_affine_axis_pair_execution; eassumption.
Qed.
Print Assumptions memory_param_affine_axis_pair_choice_execution.
