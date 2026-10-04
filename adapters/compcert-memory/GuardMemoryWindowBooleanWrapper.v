From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryRecursiveSource GuardMemoryBooleanRectangle GuardMemoryBooleanRectangleExecution.
From GuardMemory Require Import GuardMemoryStartedBooleanRectangle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
From GuardMemory Require Import GuardMemoryStartedBooleanWrapper.
From GuardMemory Require Import GuardMemoryWindowBooleanRectangle.
Theorem window_boolean_started_all_execution fe ge locals memory flag root counters bounds counts start live original body test :
  counters <> [] -> NoDup counters ->
  (forall identifier, In identifier counters -> ~ In identifier (bounds++root::live) /\ identifier <> flag) ->
  ~ In flag (bounds++root::live) ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  start <= hd 0 counts -> signed_range start ->
  length counters = length counts ->
  memory_nest_bindings bounds counts original -> original ! root = Some (Vint (Int.repr start)) ->
  (forall coordinates temps accepted,
    memory_started_axis_coordinates start counts coordinates ->
    memory_nest_bindings counters coordinates temps -> temp_agree (bounds++root::live) original temps ->
    temps ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals temps memory body E0 after memory Out_normal /\
      temp_agree (counters++bounds++root::live) temps after /\
      after ! flag = Some (memory_boolean_word (accepted && test coordinates))) ->
  forall current accepted,
    temp_agree (bounds++root::live) original current -> current ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals current memory (memory_boolean_started_rectangle_statement root counters bounds body) E0 after memory Out_normal /\
      temp_agree (bounds++root::live) current after /\
      after ! flag = Some (memory_boolean_word (accepted && memory_boolean_started_all_result test counts start)).
Proof.
  destruct counters as [|counter counters]; [contradiction|].
  intros NONEMPTY UNIQUE FRESH FLAG RANGES START START_RANGE LENGTH WORDS ROOT BODY current accepted FRAME INITIAL.
  destruct counts as [|upper counts]; [discriminate LENGTH|].
  destruct bounds as [|bound bounds]; [inversion WORDS|].
  inversion RANGES as [|nn ns [NONNEG RANGE] TAIL]; subst.
  eapply window_boolean_started_rectangle_execution; eauto.
Qed.
Print Assumptions window_boolean_started_all_execution.
