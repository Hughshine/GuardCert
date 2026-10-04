From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestExamples AffineNestLoopEncoding AffineNestBoundEncoding.
Import ListNotations.
Local Open Scope Z_scope.

Example three_level_loop_uses_real_prefixes :
  affine_lower_nest affine_example_nest [] [4%positive;7%positive;8%positive]
    (L.Var 3) (L.Seq L.SNil)=
  Some(L.Loop (L.Var 3) (L.Var 0)
    (L.Loop (L.Constant 0) (L.Sum (L.Var 0) (L.Var 2))
      (L.Loop (L.Constant 0) (L.Sum (L.Var 0) (L.Var 4)) (L.Seq L.SNil)))).
Proof. vm_compute; reflexivity. Qed.

Example child_bounds_may_be_negative :
  check_affine_bound_cap [1%positive;4%positive;7%positive;8%positive]
    [MemoryNested.A.Interval (-2) 2;MemoryNested.A.Interval 1 3;
      MemoryNested.A.Interval (-2) 2;MemoryNested.A.Interval 0 4]
    affine_example_first 4=true.
Proof. vm_compute; reflexivity. Qed.

Example grandchild_uses_both_levels_and_parameters :
  check_affine_bound_cap [2%positive;1%positive;4%positive;7%positive;8%positive]
    [MemoryNested.A.Interval 0 3;MemoryNested.A.Interval (-2) 2;MemoryNested.A.Interval 1 3;
      MemoryNested.A.Interval (-2) 2;MemoryNested.A.Interval 0 4]
    affine_example_second 7=true.
Proof. vm_compute; reflexivity. Qed.

Example overflowing_bound_interval_refused :
  check_affine_bound_cap [1%positive]
    [MemoryNested.A.Interval Int.max_signed Int.max_signed]
    (MemorySourceAdd (MemorySourceTemp 1%positive) (MemorySourceConstant 1)) Int.max_signed=false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions three_level_loop_uses_real_prefixes.
Print Assumptions child_bounds_may_be_negative.
Print Assumptions grandchild_uses_both_levels_and_parameters.
Print Assumptions overflowing_bound_interval_refused.
