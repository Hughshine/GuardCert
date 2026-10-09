From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightRegionProgress.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryDoubleLocations
  GuardMemoryDoubleHeaderFrame GuardMemoryObservationDeterminism.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_long_header_lt_constant header number :=
  Ebinop Olt (Evar header memory_long_type)
    (Econst_long (Int64.repr number) memory_long_type) memory_signed_int_type.
Definition memory_long_constant_lt_header number header :=
  Ebinop Olt (Econst_long (Int64.repr number) memory_long_type)
    (Evar header memory_long_type) memory_signed_int_type.

Lemma memory_long_header_lt_constant_execution ge locals temps memory header block word number :
  double_global_binding ge locals header block ->
  Mem.load Mint64 memory block 0 = Some (Vlong word) ->
  Int64.min_signed <= number <= Int64.max_signed ->
  expression_test (memory_long_header_lt_constant header number)
    (Entry ge locals temps memory) (Int64.signed word <? number).
Proof.
  intros BIND LOAD RANGE; exists (Val.of_bool (Int64.signed word <? number)); split.
  - eapply memory_long_test_execution; try reflexivity; try exact RANGE.
    + apply Int64.signed_range.
    + rewrite Int64.repr_signed; eapply memory_global_long_execution; eauto.
    + constructor.
  - destruct (Int64.signed word <? number); reflexivity.
Qed.
Lemma memory_long_constant_lt_header_execution ge locals temps memory header block word number :
  double_global_binding ge locals header block ->
  Mem.load Mint64 memory block 0 = Some (Vlong word) ->
  Int64.min_signed <= number <= Int64.max_signed ->
  expression_test (memory_long_constant_lt_header number header)
    (Entry ge locals temps memory) (number <? Int64.signed word).
Proof.
  intros BIND LOAD RANGE; exists (Val.of_bool (number <? Int64.signed word)); split.
  - eapply memory_long_test_execution; try reflexivity; try exact RANGE.
    + apply Int64.signed_range.
    + constructor.
    + rewrite Int64.repr_signed; eapply memory_global_long_execution; eauto.
  - destruct (number <? Int64.signed word); reflexivity.
Qed.

Definition memory_long_range_accept word limit :=
  if Int64.signed word <? 0 then false else negb (limit <? Int64.signed word).
Definition memory_long_range_tree header limit :=
  Test (memory_long_header_lt_constant header 0) (Decision false)
    (Test (memory_long_constant_lt_header limit header) (Decision false) (Decision true)).

Lemma memory_long_range_accept_spec word limit :
  memory_long_range_accept word limit = true <-> 0 <= Int64.signed word <= limit.
Proof.
  unfold memory_long_range_accept.
  destruct (Int64.signed word <? 0) eqn:LOWER.
  - apply Z.ltb_lt in LOWER; split; [discriminate|lia].
  - apply Z.ltb_ge in LOWER; rewrite negb_true_iff, Z.ltb_ge; lia.
Qed.
Lemma memory_int_nonnegative_long_range value : 0 <= value <= Int.max_signed ->
  Int64.min_signed <= value <= Int64.max_signed.
Proof.
  change (0 <= value <= 2147483647 -> -9223372036854775808 <= value <= 9223372036854775807); lia.
Qed.
Theorem memory_long_range_tree_execution ge locals temps memory header block word limit :
  double_global_binding ge locals header block ->
  Mem.load Mint64 memory block 0 = Some (Vlong word) -> 0 <= limit <= Int.max_signed ->
  decision_run (Entry ge locals temps memory) (memory_long_range_tree header limit)
    (memory_long_range_accept word limit).
Proof.
  intros BIND LOAD RANGE; unfold memory_long_range_tree, memory_long_range_accept.
  eapply run_test with (b := (Int64.signed word <? 0)).
  - eapply memory_long_header_lt_constant_execution; eauto.
    change (-9223372036854775808 <= 0 <= 9223372036854775807); lia.
  - destruct (Int64.signed word <? 0); [constructor|].
    eapply run_test with (b := (limit <? Int64.signed word)).
    + eapply memory_long_constant_lt_header_execution; eauto using memory_int_nonnegative_long_range.
    + destruct (limit <? Int64.signed word); constructor.
Qed.

Definition memory_long_to_int header := Ecast (Evar header memory_long_type) memory_signed_int_type.
Lemma memory_long_to_int_execution ge locals temps memory header block word :
  double_global_binding ge locals header block -> Mem.load Mint64 memory block 0 = Some (Vlong word) ->
  eval_expr ge locals temps memory (memory_long_to_int header) (Vint (Int64.loword word)).
Proof.
  intros BIND LOAD; eapply eval_Ecast; [eapply memory_global_long_execution; eauto|reflexivity].
Qed.
Theorem memory_long_accepted_int_exact word limit :
  0 <= limit <= Int.max_signed -> memory_long_range_accept word limit = true ->
  Int64.loword word = Int.repr (Int64.signed word) /\
  Int.signed (Int64.loword word) = Int64.signed word.
Proof.
  intros LIMIT ACCEPT; apply memory_long_range_accept_spec in ACCEPT.
  assert (UNSIGNED : Int64.signed word = Int64.unsigned word).
  { apply Int64.signed_eq_unsigned; apply (proj1 (Int64.signed_positive word)); lia. }
  unfold Int64.loword; rewrite <- UNSIGNED; split; [reflexivity|].
  apply Int.signed_repr; pose proof Int.min_signed_neg; lia.
Qed.

Definition memory_capture_flag flag (accepted : bool) :=
  Sset flag (Econst_int (if accepted then Int.one else Int.zero) memory_signed_int_type).
Definition memory_long_range_capture header cache flag limit :=
  tree_statement (memory_long_range_tree header limit)
    (Ssequence (Sset cache (memory_long_to_int header)) (memory_capture_flag flag true))
    (memory_capture_flag flag false).
Definition memory_long_range_captured (temps : temp_env) cache flag word limit :=
  PTree.set flag (Vint (if memory_long_range_accept word limit then Int.one else Int.zero))
    (if memory_long_range_accept word limit then PTree.set cache (Vint (Int64.loword word)) temps else temps).

Lemma memory_capture_flag_execution fe ge locals temps memory flag accepted :
  exec_stmt fe ge locals temps memory (memory_capture_flag flag accepted) E0
    (PTree.set flag (Vint (if accepted then Int.one else Int.zero)) temps) memory Out_normal.
Proof. constructor; constructor. Qed.
Theorem memory_long_range_capture_execution fe ge locals temps memory header block cache flag word limit :
  double_global_binding ge locals header block -> Mem.load Mint64 memory block 0 = Some (Vlong word) ->
  0 <= limit <= Int.max_signed ->
  exec_stmt fe ge locals temps memory (memory_long_range_capture header cache flag limit) E0
    (memory_long_range_captured temps cache flag word limit) memory Out_normal.
Proof.
  intros BIND LOAD LIMIT; unfold memory_long_range_capture, memory_long_range_captured.
  eapply decision_fragment_run; [eapply memory_long_range_tree_execution; eauto|].
  destruct (memory_long_range_accept word limit).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + constructor; eapply memory_long_to_int_execution; eauto.
    + apply memory_capture_flag_execution.
  - apply memory_capture_flag_execution.
Qed.

Lemma memory_long_range_capture_writes header cache flag limit :
  writes_only [cache;flag] (memory_long_range_capture header cache flag limit).
Proof.
  unfold memory_long_range_capture, memory_long_range_tree, memory_capture_flag; cbn [tree_statement].
  repeat first [apply writes_if|apply writes_sequence|apply writes_set]; cbn; auto.
Qed.

Print Assumptions memory_long_range_accept_spec.
Print Assumptions memory_long_range_tree_execution.
Print Assumptions memory_long_to_int_execution.
Print Assumptions memory_long_accepted_int_exact.
Print Assumptions memory_long_range_capture_execution.
Print Assumptions memory_long_range_capture_writes.
