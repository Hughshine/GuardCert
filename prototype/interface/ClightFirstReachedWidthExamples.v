From Stdlib Require Import List ZArith.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceEndpoints GuardMemoryParametricChecker.
From GuardInterface Require Import ClightFirstReachedWidth.
Import ListNotations.
Local Open Scope Z_scope.

(** Closed non-vacuity and refusal computations for the condition library.
    They are not installed-compiler or native optimization acceptance results. *)
Definition reached_example_expression:=MemorySourceAdd(MemorySourceTemp 1%positive)(MemorySourceTemp 3%positive).
Definition reached_example_context:=[2%positive;3%positive].
Definition reached_example_bounds:=[MemoryNested.A.Interval 1 4;MemoryNested.A.Interval(-2)4].
Definition reached_example_test skip:=first_reached_width_test(-2)8 skip
  (L.Var 1)(L.Sum(L.Sum(L.Var O)(L.Constant(-1)))(L.Var 1))
  (L.Sum(L.Constant(Z.of_nat skip-1))(L.Var 1))
  (L.Sum(L.Constant(Z.of_nat skip))(L.Var 1)).

Example first_reached_width_guard_compiles :
  match compile_first_reached_width(-2)8 1 1%positive reached_example_context reached_example_bounds
    reached_example_expression with Some _=>true|None=>false end=true.
Proof. vm_compute; reflexivity. Qed.

Example zero_first_child_new_condition_accepts_old_width_refuses :
  L.eval_test [3;0](reached_example_test 1)=true /\
  memory_source_width_model 8 1%positive reached_example_context reached_example_expression [3;0]=false.
Proof. vm_compute; split; reflexivity. Qed.

Example negative_then_zero_prefix_condition_accepts :
  L.eval_test [3;-1](reached_example_test 2)=true.
Proof. vm_compute; reflexivity. Qed.

Example unavailable_later_child_refused : L.eval_test [1;0](reached_example_test 1)=false.
Proof. vm_compute; reflexivity. Qed.

Example falsely_proposed_empty_prefix_refused : L.eval_test [3;0](reached_example_test 2)=false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions first_reached_width_guard_compiles.
Print Assumptions zero_first_child_new_condition_accepts_old_width_refuses.
Print Assumptions negative_then_zero_prefix_condition_accepts.
Print Assumptions unavailable_later_child_refused.
Print Assumptions falsely_proposed_empty_prefix_refused.
