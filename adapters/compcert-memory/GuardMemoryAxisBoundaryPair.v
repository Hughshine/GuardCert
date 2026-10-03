From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryBooleanScan GuardMemoryFootprintCapabilities GuardMemoryNaryAffineExpressions GuardMemoryRecursiveSource
  GuardMemoryAffineAxisPairScan.
From GuardMemory Require Import GuardMemoryAxisBoundaryMath GuardMemoryAxisBoundaryCells GuardMemoryAxisBoundaryMasks.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_axis_boundary_pair_statement layout counters zero flag bounds first second first_expression second_expression :=
  Ssequence (Sset zero (Econst_int Int.zero type_int32s))
    (memory_affine_axis_boundary_masks_statement layout counters zero flag bounds
      (memory_axis_boundary_masks (length layout)) first second first_expression second_expression).

Theorem memory_affine_axis_boundary_pair_execution first_expression second_expression first_term second_term
  layout counters zero bounds counts fe ge locals original current memory extent first second flag live accepted :
  memory_encode_nary_index layout first_expression = Some first_term ->
  memory_encode_nary_index layout second_expression = Some second_term ->
  fst first_term = fst second_term ->
  NoDup layout -> NoDup counters -> length layout = length counts -> length counters = length counts ->
  first <> second -> extent <= Int.max_signed+1 ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  (forall identifier, In identifier counters -> ~ In identifier (bounds++first::second::live) /\ identifier <> flag) ->
  ~ In zero counters -> ~ In zero (bounds++first::second::live) -> zero <> flag ->
  ~ In flag (bounds++first::second::live) ->
  memory_nest_bindings bounds counts original ->
  temp_agree (bounds++first::second::live) original current -> current ! flag = Some (memory_boolean_word accepted) ->
  (forall coordinates, Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell first (memory_nary_index_value first_term coordinates)) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell second (memory_nary_index_value second_term coordinates))) ->
  exists after,
    exec_stmt fe ge locals current memory
      (memory_affine_axis_boundary_pair_statement layout counters zero flag bounds first second first_expression second_expression)
      E0 after memory Out_normal /\
    temp_agree (bounds++first::second::live) current after /\
    after ! flag = Some (memory_boolean_word (accepted && memory_affine_axis_pair_check
      (memory_multi_pointer_locations original extent) counts first second first_term second_term)).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE COEFFICIENTS SOURCE_UNIQUE COUNTER_UNIQUE SOURCE_LENGTH COUNTER_LENGTH DISTINCT EXTENT
    RANGES FRESH ZERO_COUNTER ZERO_PUBLIC ZERO_FLAG FLAG_FRESH WORDS FRAME FLAG CAPS.
  assert (ALL_FRESH : forall identifier, In identifier counters ->
    ~ In identifier (bounds++zero::first::second::live) /\ identifier <> flag).
  { intros identifier MEMBER; destruct (FRESH identifier MEMBER) as [PUBLIC NOT_FLAG]; split; [|exact NOT_FLAG].
    intro BAD; apply in_app_or in BAD as [BAD|BAD].
    - apply PUBLIC; apply in_or_app; left; exact BAD.
    - cbn in BAD; destruct BAD as [SAME|BAD].
      + subst identifier; apply ZERO_COUNTER; exact MEMBER.
      + apply PUBLIC; apply in_or_app; right; exact BAD. }
  assert (ALL_FLAG : ~ In flag (bounds++zero::first::second::live)).
  { intro BAD; apply in_app_or in BAD as [BAD|BAD].
    - apply FLAG_FRESH; apply in_or_app; left; exact BAD.
    - cbn in BAD; destruct BAD as [SAME|BAD];
        [congruence|apply FLAG_FRESH; apply in_or_app; right; exact BAD]. }
  set (initialized := PTree.set zero (Vint Int.zero) current).
  assert (INIT_FRAME : temp_agree (bounds++first::second::live) current initialized) by (apply temp_agree_set; exact ZERO_PUBLIC).
  assert (INIT_ZERO : initialized ! zero = Some (Vint Int.zero)) by (unfold initialized; apply PTree.gss).
  assert (INIT_FLAG : initialized ! flag = Some (memory_boolean_word accepted)).
  { unfold initialized; rewrite PTree.gso by congruence; exact FLAG. }
  destruct (@memory_affine_axis_boundary_masks_execution first_expression second_expression first_term second_term
    layout counters zero bounds counts (memory_axis_boundary_masks (length counts))
    fe ge locals original memory extent first second flag live
    FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE COUNTER_UNIQUE SOURCE_LENGTH COUNTER_LENGTH DISTINCT EXTENT
    RANGES ALL_FRESH ALL_FLAG WORDS CAPS (memory_axis_boundary_masks_valid (length counts))
    initialized accepted ltac:(eapply temp_agree_trans; eassumption) INIT_ZERO INIT_FLAG)
    as [after [RUN [AFTER_FRAME AFTER_FLAG]]].
  assert (COUNTS : Forall (fun count => 0 <= count) counts).
  { eapply Forall_impl; [|exact RANGES]; intros count [POS RANGE]; exact POS. }
  change (after ! flag = Some (memory_boolean_word (accepted && memory_affine_axis_boundary_pair_check
    (memory_multi_pointer_locations original extent) counts first second first_term second_term))) in AFTER_FLAG.
  rewrite (@memory_affine_axis_boundary_pair_exact original extent memory counts first second first_term second_term
    DISTINCT COEFFICIENTS COUNTS CAPS) in AFTER_FLAG.
  rewrite <-SOURCE_LENGTH in RUN.
  exists after; split.
  - unfold memory_affine_axis_boundary_pair_statement.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor; constructor|exact RUN].
  - split; [|exact AFTER_FLAG]; eapply temp_agree_trans; [exact INIT_FRAME|].
    eapply temp_agree_weaken; [|exact AFTER_FRAME]; intros identifier MEMBER.
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app;
      [left; exact MEMBER|right; cbn; auto].
Qed.
Print Assumptions memory_affine_axis_boundary_pair_execution.
