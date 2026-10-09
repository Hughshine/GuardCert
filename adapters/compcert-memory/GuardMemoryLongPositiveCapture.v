From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongRangeCapture.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A positive capture is a prerequisite for observing a later nested bound.
    It refines the existing range service without supplying its read license. *)
Definition memory_long_positive_accept word limit :=
  (0<?Int64.signed word) && memory_long_range_accept word limit.
Definition memory_long_positive_capture header cache flag limit :=
  Sifthenelse (memory_long_constant_lt_header 0 header)
    (memory_long_range_capture header cache flag limit) (memory_capture_flag flag false).
Definition memory_long_positive_captured temps cache flag word limit :=
  if 0<?Int64.signed word then memory_long_range_captured temps cache flag word limit
  else PTree.set flag (Vint Int.zero) temps.
Theorem memory_long_positive_capture_execution fe ge locals temps memory header bound_block cache flag word limit :
  double_global_binding ge locals header bound_block ->
  Mem.load Mint64 memory bound_block 0=Some (Vlong word) -> 0<=limit<=Int.max_signed ->
  exec_stmt fe ge locals temps memory (memory_long_positive_capture header cache flag limit) E0
    (memory_long_positive_captured temps cache flag word limit) memory Out_normal.
Proof.
  intros BINDING LOAD LIMIT.
  destruct (@memory_long_constant_lt_header_execution ge locals temps memory header bound_block word 0
    BINDING LOAD ltac:(change (-9223372036854775808<=0<=9223372036854775807); lia)) as [value [EVAL BOOL]].
  unfold memory_long_positive_capture,memory_long_positive_captured.
  eapply exec_Sifthenelse with (b:=(0<?Int64.signed word)); [exact EVAL|exact BOOL|].
  destruct (0<?Int64.signed word); [eapply memory_long_range_capture_execution; eassumption|apply memory_capture_flag_execution].
Qed.
Theorem memory_long_positive_accept_spec word limit :
  memory_long_positive_accept word limit=true <-> 1<=Int64.signed word<=limit.
Proof.
  unfold memory_long_positive_accept; rewrite andb_true_iff,Z.ltb_lt,memory_long_range_accept_spec; lia.
Qed.
Lemma memory_long_positive_captured_flag temps cache flag word limit :
  (memory_long_positive_captured temps cache flag word limit) ! flag=
  Some (Vint (if memory_long_positive_accept word limit then Int.one else Int.zero)).
Proof.
  unfold memory_long_positive_captured,memory_long_positive_accept,memory_long_range_captured.
  destruct (0<?Int64.signed word); cbn [andb]; apply PTree.gss.
Qed.
Theorem memory_long_positive_captured_cache temps cache flag word limit :
  cache<>flag -> 0<=limit<=Int.max_signed -> memory_long_positive_accept word limit=true ->
  (memory_long_positive_captured temps cache flag word limit) ! cache=
    Some (Vint (Int.repr (Int64.signed word))) /\ Int64.loword word=Int.repr (Int64.signed word) /\
    Int.signed (Int64.loword word)=Int64.signed word.
Proof.
  intros FRESH LIMIT ACCEPT.
  unfold memory_long_positive_accept in ACCEPT; apply andb_true_iff in ACCEPT as [POSITIVE RANGE].
  unfold memory_long_positive_captured,memory_long_range_captured; rewrite POSITIVE,RANGE.
  destruct (@memory_long_accepted_int_exact word limit LIMIT RANGE) as [WORD SIGNED].
  rewrite PTree.gso by congruence; rewrite PTree.gss.
  split; [rewrite WORD; reflexivity|split; assumption].
Qed.
Lemma memory_long_positive_captured_frame temps cache flag word limit key :
  key<>cache -> key<>flag ->
  (memory_long_positive_captured temps cache flag word limit) ! key=temps ! key.
Proof.
  intros CACHE FLAG; unfold memory_long_positive_captured,memory_long_range_captured.
  destruct (0<?Int64.signed word), (memory_long_range_accept word limit); rewrite !PTree.gso by congruence; reflexivity.
Qed.

Print Assumptions memory_long_positive_capture_execution.
Print Assumptions memory_long_positive_accept_spec.
Print Assumptions memory_long_positive_captured_flag.
Print Assumptions memory_long_positive_captured_cache.
Print Assumptions memory_long_positive_captured_frame.
