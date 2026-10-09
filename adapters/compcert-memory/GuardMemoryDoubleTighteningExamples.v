From Stdlib Require Import List ZArith.
From GuardMemory Require Import GuardMemoryDoubleTightenedCandidate GuardMemoryDoublePolyhedral.
Import ListNotations.
Local Open Scope Z_scope.
Module TL := DoubleAssignmentIRs.Loop.
Definition tightening_tile_test numerator divisor :=
  TL.And (TL.LE (TL.Constant 0) (TL.Var 0))
    (TL.LE (TL.Mult divisor (TL.Sum (TL.Var 0) (TL.Constant 1))) numerator).
Definition tightening_tile_reference :=
  TL.Loop (TL.Constant 0) (TL.Constant 4)
    (TL.Guard (tightening_tile_test (TL.Sum (TL.Var 1) (TL.Constant 31)) 32) (TL.Seq TL.SNil)).
Definition tightening_tile_actual := double_rectangular_tightened_loop [96] tightening_tile_reference.
Example tightening_retains_runtime_parameter : tightening_tile_actual=
  TL.Loop (TL.Constant 0) (TL.Div (TL.Sum (TL.Var 0) (TL.Constant 31)) 32)
    (TL.Guard (tightening_tile_test (TL.Sum (TL.Var 1) (TL.Constant 31)) 32) (TL.Seq TL.SNil)).
Proof. vm_compute; reflexivity. Qed.
Example tightening_tile_boundaries :
  map (fun n=>TL.eval_expr [n] (TL.Div (TL.Sum (TL.Var 0) (TL.Constant 31)) 32))
    [0;1;31;32;33;95;96]=[0;1;1;1;2;3;3].
Proof. vm_compute; reflexivity. Qed.
Example tightening_rejects_overflowing_numerator :
  double_rectangular_tightened_loop [2147483647] tightening_tile_reference=tightening_tile_reference.
Proof. vm_compute; reflexivity. Qed.
Example tightening_rejects_negative_numerator :
  DoubleTightening.tightened_upper [DoubleTightening.A.Interval (-32) 96] (TL.Constant 4)
    (TL.Guard (tightening_tile_test (TL.Sum (TL.Var 1) (TL.Constant 31)) 32) (TL.Seq TL.SNil))=
    TL.Constant 4.
Proof. vm_compute; reflexivity. Qed.
Example tightening_rejects_current_iterator_dependency :
  DoubleTightening.guard_upper (tightening_tile_test (TL.Sum (TL.Var 0) (TL.Constant 31)) 32)=None.
Proof. reflexivity. Qed.
Example tightening_rejects_disjunctive_license :
  DoubleTightening.guard_upper (TL.Or
    (tightening_tile_test (TL.Sum (TL.Var 1) (TL.Constant 31)) 32)
    (TL.LE (TL.Constant 0) (TL.Constant 1)))=None.
Proof. reflexivity. Qed.
Example tightening_rejects_zero_divisor :
  DoubleTightening.guard_upper (tightening_tile_test (TL.Var 1) 0)=None.
Proof. reflexivity. Qed.
Example tightening_rejects_bound_outside_validated_enclosure :
  double_rectangular_tightened_loop [160] tightening_tile_reference=tightening_tile_reference.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions tightening_retains_runtime_parameter.
Print Assumptions tightening_tile_boundaries.
Print Assumptions tightening_rejects_overflowing_numerator.
Print Assumptions tightening_rejects_negative_numerator.
Print Assumptions tightening_rejects_current_iterator_dependency.
Print Assumptions tightening_rejects_disjunctive_license.
Print Assumptions tightening_rejects_zero_divisor.
Print Assumptions tightening_rejects_bound_outside_validated_enclosure.
