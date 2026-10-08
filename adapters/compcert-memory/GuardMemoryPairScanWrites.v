From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryBooleanRectangleExecution
  GuardMemoryBooleanPairRectangle GuardMemoryMultiTensorPairScan.
Import ListNotations.
Set Implicit Arguments.

Lemma counted_loop_private_writes allowed iterator bound body :
  In iterator allowed -> writes_only allowed body -> writes_only allowed (counted_loop iterator bound body).
Proof.
  intros ITERATOR BODY; unfold counted_loop,counter_increment; apply writes_loop.
  - apply writes_if; [exact BODY|constructor].
  - apply writes_set; exact ITERATOR.
Qed.

Lemma memory_boolean_rectangle_writes counters bounds body allowed :
  writes_only allowed body ->
  writes_only (counters++allowed) (memory_boolean_rectangle_statement counters bounds body).
Proof.
  revert bounds; induction counters as [|counter counters IH]; intros [|bound bounds] BODY;
    cbn [memory_boolean_rectangle_statement app]; try assumption; try solve [constructor].
  apply writes_sequence.
  - apply writes_set; cbn; auto.
  - apply counted_loop_private_writes; [cbn; auto|].
    eapply writes_only_weaken; [|apply IH; exact BODY].
    intros identifier MEMBER; cbn; auto.
Qed.

Theorem memory_boolean_pair_rectangle_writes left right bounds body allowed :
  writes_only allowed body ->
  writes_only (left++right++allowed) (memory_boolean_pair_rectangle_statement left right bounds body).
Proof.
  intro BODY; unfold memory_boolean_pair_rectangle_statement.
  apply memory_boolean_rectangle_writes, memory_boolean_rectangle_writes; exact BODY.
Qed.

Theorem multi_tensor_pair_scan_writes dimensions left right bounds flag first second :
  writes_only (left++right++[flag]) (multi_tensor_pair_scan dimensions left right bounds flag first second).
Proof.
  unfold multi_tensor_pair_scan; apply memory_boolean_pair_rectangle_writes.
  unfold memory_boolean_test_body; apply writes_if; [constructor|apply writes_set; cbn; auto].
Qed.

Print Assumptions counted_loop_private_writes.
Print Assumptions memory_boolean_rectangle_writes.
Print Assumptions memory_boolean_pair_rectangle_writes.
Print Assumptions multi_tensor_pair_scan_writes.
