From Stdlib Require Import List ZArith.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryAffineSourceExpressions
  GuardMemoryParametricChecker GuardMemoryZeroWidthModel.
From GuardInterface Require Import ClightFirstReachedWidth.
Import ListNotations.
Local Open Scope Z_scope.

(** Model-domain computations, not installed/native acceptance evidence. *)
Definition zero_width_example_expression:=MemorySourceAdd
  (MemorySourceTemp 1%positive)(MemorySourceTemp 3%positive).
Definition zero_width_example_context:=[2%positive;3%positive].

Example zero_first_width_new_model_accepts_old_refuses :
  memory_source_zero_width_model 8 1%positive zero_width_example_context zero_width_example_expression [3;0]=true /\
  memory_source_width_model 8 1%positive zero_width_example_context zero_width_example_expression [3;0]=false.
Proof. vm_compute; split; reflexivity. Qed.

Example negative_first_width_model_refuses :
  memory_source_zero_width_model 8 1%positive zero_width_example_context zero_width_example_expression [3;-1]=false.
Proof. vm_compute; reflexivity. Qed.

Example endpoint_cap_violation_model_refuses :
  memory_source_zero_width_model 8 1%positive zero_width_example_context zero_width_example_expression [3;7]=false.
Proof. vm_compute; reflexivity. Qed.

Example zero_last_width_model_accepts :
  memory_source_zero_width_model 8 1%positive zero_width_example_context
    (MemorySourceSub(MemorySourceTemp 3%positive)(MemorySourceTemp 1%positive)) [3;2]=true.
Proof. vm_compute; reflexivity. Qed.

Example all_empty_model_does_not_license_a_body :
  memory_source_zero_width_model 8 1%positive zero_width_example_context(MemorySourceConstant 0)[3;0]=true /\
  L.eval_test [3;0](first_reached_width_test 0 8 0
    (L.Constant 0)(L.Constant 0)(L.Constant 0)(L.Constant 0))=false.
Proof. vm_compute; split; reflexivity. Qed.

Print Assumptions zero_first_width_new_model_accepts_old_refuses.
Print Assumptions negative_first_width_model_refuses.
Print Assumptions endpoint_cap_violation_model_refuses.
Print Assumptions zero_last_width_model_accepts.
Print Assumptions all_empty_model_does_not_license_a_body.
