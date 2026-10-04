From Stdlib Require Import List ZArith.
From GuardAffineNest Require Import AffineNestPackageExamples AffineNestStaticPackage.
Import ListNotations.

Definition affine_static_example_allocated := [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive;107%positive].
Definition affine_static_example_accept allocated := match check_affine_static_package affine_memory_example_source
  affine_memory_example_parameters affine_memory_example_live allocated
  (affine_memory_example_proposal [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive] 107%positive)
  with Some _=>true|None=>false end.
Example real_three_level_static_package_accepted : affine_static_example_accept affine_static_example_allocated=true.
Proof. vm_compute; reflexivity. Qed.
Example missing_private_bound_declaration_refused :
  affine_static_example_accept [101%positive;104%positive;102%positive;105%positive;103%positive;107%positive]=false.
Proof. vm_compute; reflexivity. Qed.
Example missing_guard_result_declaration_refused :
  affine_static_example_accept [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive]=false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions real_three_level_static_package_accepted.
Print Assumptions missing_private_bound_declaration_refused.
Print Assumptions missing_guard_result_declaration_refused.
