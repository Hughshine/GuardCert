From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongRangeSource GuardMemoryLongRangeHeader
  GuardMemoryLongExpressionCapture GuardMemoryLongControl GuardMemoryLongRangeCapture.
Set Implicit Arguments.
Local Open Scope Z_scope.

Example original_fusion1_interval_counts :
  memory_long_range_count 1 (4096-2)=4093%nat /\ memory_long_range_count 2 (4096-3)=4091%nat.
Proof. vm_compute; auto. Qed.
Example empty_nonzero_interval_preserves_start : memory_long_range_count 5 3=0%nat /\ Z.max 5 3=5.
Proof. vm_compute; auto. Qed.
Example negative_interval_is_nonempty : memory_long_range_count (-3) (-1)=2%nat.
Proof. vm_compute; reflexivity. Qed.
Example negative_expression_is_accepted_exactly :
  memory_long_expression_accept (Int64.repr (-2)) (-5) (-1)=true /\
  Int.signed (Int64.loword (Int64.repr (-2)))=(-2).
Proof. vm_compute; auto. Qed.
Example common_offset_bound_is_accepted :
  memory_long_expression_accept (Int64.sub (Int64.repr 4096) (Int64.repr 2)) 0 4096=true /\
  Int64.signed (Int64.sub (Int64.repr 4096) (Int64.repr 2))=4094.
Proof. vm_compute; auto. Qed.
Example subtraction_underflow_refuses_i32_encoding :
  memory_long_expression_accept (Int64.sub (Int64.repr Int64.min_signed) (Int64.repr 2))
    Int.min_signed Int.max_signed=false.
Proof. vm_compute; reflexivity. Qed.
Example subtraction_overflow_refuses_i32_encoding :
  memory_long_expression_accept (Int64.sub (Int64.repr Int64.max_signed) (Int64.repr (-2)))
    Int.min_signed Int.max_signed=false.
Proof. vm_compute; reflexivity. Qed.
Example multiplication_can_wrap_into_an_accepted_i32_result :
  let input := Int64.repr (Int64.min_signed+1) in
  let result := Int64.mul input (Int64.repr 2) in
  memory_long_expression_accept result Int.min_signed Int.max_signed=true /\
  Int64.signed input*2<>Int64.signed result.
Proof. vm_compute; split; [reflexivity|discriminate]. Qed.

Lemma contradictory_expression_interval_refuses word : memory_long_expression_accept word 1 0=false.
Proof.
  apply not_true_is_false; intro ACCEPT; apply memory_long_expression_accept_spec in ACCEPT; lia.
Qed.
Example contradictory_guard_has_actual_readonly_execution fe ge locals temps memory code cache flag word :
  typeof code=memory_long_type -> eval_expr ge locals temps memory code (Vlong word) ->
  exec_stmt fe ge locals temps memory (memory_long_expression_capture code cache flag 1 0) E0
    (PTree.set flag (Vint Int.zero) temps) memory Out_normal.
Proof.
  intros TYPE SAFE.
  pose proof (@memory_long_expression_capture_execution fe ge locals temps memory code cache flag word 1 0
    TYPE SAFE ltac:(change (-2147483648<=1<=2147483647); lia)
    ltac:(change (-2147483648<=0<=2147483647); lia)) as RUN.
  unfold memory_long_expression_captured in RUN; rewrite contradictory_expression_interval_refuses in RUN; exact RUN.
Qed.

Print Assumptions original_fusion1_interval_counts.
Print Assumptions empty_nonzero_interval_preserves_start.
Print Assumptions negative_interval_is_nonempty.
Print Assumptions negative_expression_is_accepted_exactly.
Print Assumptions common_offset_bound_is_accepted.
Print Assumptions subtraction_underflow_refuses_i32_encoding.
Print Assumptions subtraction_overflow_refuses_i32_encoding.
Print Assumptions multiplication_can_wrap_into_an_accepted_i32_result.
Print Assumptions contradictory_expression_interval_refuses.
Print Assumptions contradictory_guard_has_actual_readonly_execution.
