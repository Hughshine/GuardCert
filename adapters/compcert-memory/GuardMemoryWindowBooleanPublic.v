From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryRecursiveSource GuardMemoryBooleanRectangle GuardMemoryBooleanRectangleExecution.
From GuardMemory Require Import GuardMemoryStartedBooleanRectangle GuardMemoryStartedBooleanWrapper.
From GuardMemory Require Import GuardMemoryWindowBooleanRectangle GuardMemoryWindowBooleanWrapper.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Theorem window_boolean_started_public_execution fe ge locals memory flag root counters bounds counts start live original body test :
  counters <> [] -> In root live -> start <= hd 0 counts -> signed_range start ->
  original ! root = Some (Vint (Int.repr start)) ->
  NoDup counters ->
  (forall identifier, In identifier counters -> ~ In identifier (bounds++live) /\ identifier <> flag) ->
  ~ In flag (bounds++live) -> Forall (fun count => 0 <= count /\ signed_range count) counts ->
  length counters = length counts -> memory_nest_bindings bounds counts original ->
  (forall coordinates temps accepted,
    memory_started_axis_coordinates start counts coordinates ->
    memory_nest_bindings counters coordinates temps -> temp_agree (bounds++live) original temps ->
    temps ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals temps memory body E0 after memory Out_normal /\
      temp_agree (counters++bounds++live) temps after /\
      after ! flag = Some (memory_boolean_word (accepted && test coordinates))) ->
  forall current accepted,
    temp_agree (bounds++live) original current -> current ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals current memory (memory_boolean_started_rectangle_statement root counters bounds body) E0 after memory Out_normal /\
      temp_agree (bounds++live) current after /\
      after ! flag = Some (memory_boolean_word (accepted && memory_boolean_started_all_result test counts start)).
Proof.
  intros NONEMPTY PUBLIC START START_RANGE ROOT UNIQUE FRESH FLAG RANGES LENGTH WORDS BODY current accepted FRAME INITIAL.
  assert (INCLUDE : forall identifier, In identifier (bounds++root::live) -> In identifier (bounds++live)).
  { intros identifier MEMBER; repeat rewrite in_app_iff in *; cbn in MEMBER; intuition congruence. }
  assert (NEW_FRESH : forall identifier, In identifier counters -> ~ In identifier (bounds++root::live) /\ identifier <> flag).
  { intros identifier MEMBER; destruct (FRESH identifier MEMBER) as [PRIVATE NOT_FLAG]; split; [intro BAD; apply PRIVATE; apply INCLUDE; exact BAD|exact NOT_FLAG]. }
  assert (NEW_FLAG : ~ In flag (bounds++root::live)) by (intro BAD; apply FLAG; apply INCLUDE; exact BAD).
  assert (NEW_FRAME : temp_agree (bounds++root::live) original current).
  { eapply temp_agree_weaken; [exact INCLUDE|exact FRAME]. }
  assert (NEW_BODY : forall coordinates temps before,
    memory_started_axis_coordinates start counts coordinates ->
    memory_nest_bindings counters coordinates temps -> temp_agree (bounds++root::live) original temps ->
    temps ! flag = Some (memory_boolean_word before) ->
    exists after, exec_stmt fe ge locals temps memory body E0 after memory Out_normal /\
      temp_agree (counters++bounds++root::live) temps after /\
      after ! flag = Some (memory_boolean_word (before && test coordinates))).
  { intros coordinates temps before DOMAIN BINDINGS CURRENT GOOD.
    assert (OLD_FRAME : temp_agree (bounds++live) original temps).
    { eapply temp_agree_weaken; [|exact CURRENT]; intros identifier MEMBER;
        apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app; [left; exact MEMBER|right; cbn; auto]. }
    destruct (BODY coordinates temps before DOMAIN BINDINGS OLD_FRAME GOOD) as [after [RUN [AFTER RESULT]]].
    exists after; split; [exact RUN|]; split; [|exact RESULT].
    eapply temp_agree_weaken; [|exact AFTER]; intros identifier MEMBER.
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; [apply in_or_app; left; exact MEMBER|].
    apply in_app_or in MEMBER as [MEMBER|MEMBER]; [apply in_or_app; right; apply in_or_app; left; exact MEMBER|].
    apply in_or_app; right; apply in_or_app; right.
    cbn in MEMBER; destruct MEMBER as [SAME|MEMBER]; [subst identifier; exact PUBLIC|exact MEMBER]. }
  destruct (@window_boolean_started_all_execution fe ge locals memory flag root counters bounds counts start live original body test
    NONEMPTY UNIQUE NEW_FRESH NEW_FLAG RANGES START START_RANGE LENGTH WORDS ROOT NEW_BODY current accepted NEW_FRAME INITIAL)
    as [after [RUN [AFTER RESULT]]].
  exists after; split; [exact RUN|]; split; [|exact RESULT].
  eapply temp_agree_weaken; [|exact AFTER]; intros identifier MEMBER; repeat rewrite in_app_iff in *; cbn; intuition.
Qed.
Print Assumptions window_boolean_started_public_execution.
