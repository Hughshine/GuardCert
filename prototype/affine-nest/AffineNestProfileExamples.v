From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From GuardAffineNest Require Import AffineNestExamples AffineNestProfile.
Import ListNotations.
Local Open Scope Z_scope.

Definition affine_example_parameter_ranges := [(1,4);(-2,3);(0,5)].
Definition affine_example_axis_ranges := [(-2,3);(0,4);(0,7)].
Definition affine_example_leaf_layout := [1%positive;2%positive;3%positive;4%positive;7%positive;8%positive].
Definition affine_example_profile_check parameter_ranges axis_ranges leaf_bounds :=
  check_affine_math_profile affine_example_nest [] [4%positive;7%positive;8%positive]
    [] parameter_ranges axis_ranges leaf_bounds affine_example_leaf_layout.

Example three_level_signed_profile_accepted :
  affine_example_profile_check affine_example_parameter_ranges affine_example_axis_ranges
    (affine_example_axis_ranges++affine_example_parameter_ranges)=true.
Proof. vm_compute; reflexivity. Qed.

Example insufficient_child_cap_refused :
  affine_example_profile_check affine_example_parameter_ranges [(-2,3);(0,3);(0,7)]
    ([(-2,3);(0,3);(0,7)]++affine_example_parameter_ranges)=false.
Proof. vm_compute; reflexivity. Qed.

Example overflowing_child_bound_profile_refused :
  affine_example_profile_check [(1,4);(Int.max_signed,Int.max_signed+1);(0,5)]
    [(-2,3);(0,Int.max_signed);(0,Int.max_signed)]
    ([(-2,3);(0,Int.max_signed);(0,Int.max_signed)]++[(1,4);(Int.max_signed,Int.max_signed+1);(0,5)])=false.
Proof. vm_compute; reflexivity. Qed.

Example mismatched_leaf_box_refused :
  affine_example_profile_check affine_example_parameter_ranges affine_example_axis_ranges
    ([(0,3);(0,4);(0,7)]++affine_example_parameter_ranges)=false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions three_level_signed_profile_accepted.
Print Assumptions insufficient_child_cap_refused.
Print Assumptions overflowing_child_bound_profile_refused.
Print Assumptions mismatched_leaf_box_refused.
