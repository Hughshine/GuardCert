From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleTreeCaptureLicense GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCaptureControl
  GuardMemoryDoubleTreeCaptureReceipt GuardMemoryDoubleTreeCaptureFacts GuardMemoryLongExpressionCapture.
Import ListNotations.
Local Open Scope Z_scope.

Definition tree_capture_example_cache (header : ident) := if peq header 101%positive then 301%positive else 302%positive.
Definition tree_capture_example_lower (_ : ident) := -16.
Definition tree_capture_example_upper (_ : ident) := 16.
Definition tree_capture_example_outer := DoubleTreeBound 101%positive None.
Definition tree_capture_example_child := DoubleTreeRange true 202%positive (Int.repr 1)
  (DoubleTreeBound 102%positive None) DoubleTreeSkip.
Definition tree_capture_example_empty := DoubleTreeRange true 201%positive Int.zero
  tree_capture_example_outer tree_capture_example_child.

Example tree_capture_negative_start_active :
  double_tree_word_active (Int.repr (-5)) (DoubleTreeBound 101%positive None) (Int64.repr (-2))=true.
Proof. vm_compute; reflexivity. Qed.
Example tree_capture_negative_offset_empty :
  double_tree_word_active (Int.repr (-5)) (DoubleTreeBound 101%positive (Some (Int.repr 3))) (Int64.repr (-2))=false.
Proof. vm_compute; reflexivity. Qed.
(** Acceptance of an I32 input does not claim that N-c is itself I32. The
    widened cached comparison remains exact; candidate-domain checks follow. *)
Example tree_capture_widened_bound_exact :
  Int64.signed (double_tree_bound_word (DoubleTreeBound 101%positive (Some (Int.repr (-2147483648))))
    (Int64.repr 2147483647))=4294967295.
Proof. vm_compute; reflexivity. Qed.

Theorem tree_capture_empty_outer_no_child_load fe ge locals temps memory block :
  double_global_binding ge locals 101%positive block -> Mem.load Mint64 memory block 0=Some (Vlong Int64.zero) ->
  double_tree_flag_value temps 401%positive true ->
  exec_stmt fe ge locals temps memory
    (double_tree_capture_code tree_capture_example_empty tree_capture_example_cache 401%positive
      tree_capture_example_lower tree_capture_example_upper) E0
    (double_tree_captured temps tree_capture_example_outer tree_capture_example_cache 401%positive Int64.zero
      tree_capture_example_lower tree_capture_example_upper) memory Out_normal.
Proof.
  intros BIND LOAD FLAG.
  assert (RECEIPT : double_tree_capture_receipt ge locals memory tree_capture_example_cache 401%positive
    tree_capture_example_lower tree_capture_example_upper tree_capture_example_empty temps
    (double_tree_captured temps tree_capture_example_outer tree_capture_example_cache 401%positive Int64.zero
      tree_capture_example_lower tree_capture_example_upper) true).
  { eapply double_tree_receipt_empty; [exact FLAG|exact BIND|exact LOAD| | | |].
    - change (-2147483648<= -16<=2147483647); lia.
    - change (-2147483648<=16<=2147483647); lia.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity. }
  exact (@double_tree_capture_receipt_execution ge locals memory tree_capture_example_cache 401%positive
    tree_capture_example_lower tree_capture_example_upper tree_capture_example_empty temps _ true RECEIPT
    ltac:(intros header MEMBER; unfold tree_capture_example_cache; destruct (peq header 101%positive); discriminate) fe).
Qed.

Theorem tree_capture_refusal_skips_later_headers fe ge locals temps memory block later :
  double_global_binding ge locals 101%positive block -> Mem.load Mint64 memory block 0=Some (Vlong (Int64.repr 17)) ->
  double_tree_flag_value temps 401%positive true ->
  exec_stmt fe ge locals temps memory
    (double_tree_capture_code (DoubleTreeSequence tree_capture_example_empty later) tree_capture_example_cache 401%positive
      tree_capture_example_lower tree_capture_example_upper) E0
    (double_tree_captured temps tree_capture_example_outer tree_capture_example_cache 401%positive (Int64.repr 17)
      tree_capture_example_lower tree_capture_example_upper) memory Out_normal.
Proof.
  intros BIND LOAD FLAG.
  assert (FIRST : double_tree_capture_receipt ge locals memory tree_capture_example_cache 401%positive
    tree_capture_example_lower tree_capture_example_upper tree_capture_example_empty temps
    (double_tree_captured temps tree_capture_example_outer tree_capture_example_cache 401%positive (Int64.repr 17)
      tree_capture_example_lower tree_capture_example_upper) false).
  { eapply double_tree_receipt_refused; [exact FLAG|exact BIND|exact LOAD| | |].
    - change (-2147483648<= -16<=2147483647); lia.
    - change (-2147483648<=16<=2147483647); lia.
    - vm_compute; reflexivity. }
  assert (ALL : double_tree_capture_receipt ge locals memory tree_capture_example_cache 401%positive
    tree_capture_example_lower tree_capture_example_upper (DoubleTreeSequence tree_capture_example_empty later) temps
    (double_tree_captured temps tree_capture_example_outer tree_capture_example_cache 401%positive (Int64.repr 17)
      tree_capture_example_lower tree_capture_example_upper) false).
  { eapply double_tree_receipt_sequence; [exact FIRST|apply double_tree_receipt_disabled; exact (double_tree_capture_receipt_flag FIRST)]. }
  exact (@double_tree_capture_receipt_execution ge locals memory tree_capture_example_cache 401%positive
    tree_capture_example_lower tree_capture_example_upper _ temps _ false ALL
    ltac:(intros header MEMBER; unfold tree_capture_example_cache; destruct (peq header 101%positive); discriminate) fe).
Qed.

Print Assumptions tree_capture_negative_start_active.
Print Assumptions tree_capture_negative_offset_empty.
Print Assumptions tree_capture_widened_bound_exact.
Print Assumptions tree_capture_empty_outer_no_child_load.
Print Assumptions tree_capture_refusal_skips_later_headers.
