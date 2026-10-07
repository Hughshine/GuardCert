From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRectangularLoops ClightStraightLine ClightStructuredProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRecursiveSource GuardMemoryAffineSourceExpressions GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import ClightTensorSourceExample ClightTensorBoxExample ClightTensorRegionPackage.
Import ListNotations.
Local Open Scope Z_scope.

Definition tensor_region_demo_source := memory_nest_source tensor_source_demo_nest.
Definition tensor_region_demo_frontend_inner := MemorySourceAxis 8%positive 4%positive
  (Ssequence Sskip (Ssequence tensor_source_demo_code Sskip))
  (MemorySourceLeaf(Ssequence Sskip (Ssequence tensor_source_demo_code Sskip))).
Definition tensor_region_demo_frontend_middle := MemorySourceAxis 7%positive 3%positive
  (Ssequence Sskip (Ssequence(rectangle_reset 8%positive)
    (memory_nest_source tensor_region_demo_frontend_inner)))tensor_region_demo_frontend_inner.
Definition tensor_region_demo_frontend_nest := MemorySourceAxis 6%positive 1%positive
  (Ssequence(rectangle_reset 7%positive)(memory_nest_source tensor_region_demo_frontend_middle))tensor_region_demo_frontend_middle.
Definition tensor_region_demo_frontend_source := memory_nest_source tensor_region_demo_frontend_nest.
Definition tensor_region_demo_description := TensorRegionDescription tensor_source_demo_dimensions[2%positive;5%positive]
  9%positive 20%positive tensor_source_demo_coordinates[tensor_source_demo_coordinates]
  tensor_source_demo_value 32 tensor_box_demo_profile.
Definition tensor_region_demo_recognized source description :=
  match check_tensor_region_description source description with Some _=>true|None=>false end.
Definition tensor_region_demo_empty_profile := TensorRegionDescription tensor_source_demo_dimensions[2%positive;5%positive]
  9%positive 20%positive tensor_source_demo_coordinates[tensor_source_demo_coordinates]tensor_source_demo_value 32[].
Definition tensor_region_demo_unlicensed_dimension := TensorRegionDescription
  [TensorDimensionTemp 99%positive;TensorDimensionTemp 2%positive;TensorDimensionConstant 5][2%positive;5%positive]
  9%positive 20%positive tensor_source_demo_coordinates[tensor_source_demo_coordinates]
  tensor_source_demo_value 32 tensor_box_demo_profile.
Definition tensor_region_demo_duplicate_scalar := TensorRegionDescription tensor_source_demo_dimensions[2%positive;2%positive;5%positive]
  9%positive 20%positive tensor_source_demo_coordinates[tensor_source_demo_coordinates]
  tensor_source_demo_value 32 tensor_box_demo_profile.
Definition tensor_region_demo_wrong_reset := memory_nest_source(MemorySourceAxis 6%positive 1%positive
  (Ssequence(rectangle_reset 8%positive)(memory_nest_source tensor_source_demo_middle))tensor_source_demo_middle).
Definition tensor_region_demo_unused_scalar_leaf := Sassign tensor_source_demo_cell tensor_source_demo_cell.
Definition tensor_region_demo_unused_inner := MemorySourceAxis 8%positive 4%positive
  tensor_region_demo_unused_scalar_leaf(MemorySourceLeaf tensor_region_demo_unused_scalar_leaf).
Definition tensor_region_demo_unused_middle := MemorySourceAxis 7%positive 3%positive
  (Ssequence(rectangle_reset 8%positive)(memory_nest_source tensor_region_demo_unused_inner))tensor_region_demo_unused_inner.
Definition tensor_region_demo_unused_scalar_nest := MemorySourceAxis 6%positive 1%positive
  (Ssequence(rectangle_reset 7%positive)(memory_nest_source tensor_region_demo_unused_middle))tensor_region_demo_unused_middle.
Definition tensor_region_demo_unused_scalar_description := TensorRegionDescription tensor_source_demo_dimensions[2%positive;5%positive]
  9%positive 20%positive tensor_source_demo_coordinates[tensor_source_demo_coordinates]
  (LoadedValue 0)32 tensor_box_demo_profile.
Example tensor_region_demo_original_recognized : tensor_region_demo_recognized tensor_region_demo_source tensor_region_demo_description=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_region_demo_frontend_recognized : tensor_region_demo_recognized tensor_region_demo_frontend_source tensor_region_demo_description=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_region_demo_frontend_progress_checked : structured_progress_supported tensor_region_demo_frontend_source=true.
Proof. vm_compute; reflexivity. Qed.
Example tensor_region_demo_wrong_reset_refused : tensor_region_demo_recognized tensor_region_demo_wrong_reset tensor_region_demo_description=false.
Proof. vm_compute; reflexivity. Qed.
Example tensor_region_demo_unlicensed_dimension_refused :
  tensor_region_demo_recognized tensor_region_demo_source tensor_region_demo_unlicensed_dimension=false.
Proof. vm_compute; reflexivity. Qed.
Example tensor_region_demo_duplicate_scalar_refused :
  tensor_region_demo_recognized tensor_region_demo_source tensor_region_demo_duplicate_scalar=false.
Proof. vm_compute; reflexivity. Qed.
Example tensor_region_demo_empty_profile_refused :
  tensor_region_demo_recognized tensor_region_demo_source tensor_region_demo_empty_profile=false.
Proof. vm_compute; reflexivity. Qed.
Example tensor_region_demo_unused_scalar_refused :
  tensor_region_demo_recognized(memory_nest_source tensor_region_demo_unused_scalar_nest)tensor_region_demo_unused_scalar_description=false.
Proof. vm_compute; reflexivity. Qed.
Example tensor_region_demo_source_progress_checked : structured_progress_supported tensor_region_demo_source=true.
Proof. vm_compute; reflexivity. Qed.
Definition tensor_region_demo_source_progress := @structured_progress_supported_sound tensor_region_demo_source tensor_region_demo_source_progress_checked.
Print Assumptions tensor_region_demo_original_recognized.
Print Assumptions tensor_region_demo_frontend_recognized.
Print Assumptions tensor_region_demo_frontend_progress_checked.
Print Assumptions tensor_region_demo_wrong_reset_refused.
Print Assumptions tensor_region_demo_unlicensed_dimension_refused.
Print Assumptions tensor_region_demo_duplicate_scalar_refused.
Print Assumptions tensor_region_demo_empty_profile_refused.
Print Assumptions tensor_region_demo_unused_scalar_refused.
Print Assumptions tensor_region_demo_source_progress_checked.
Print Assumptions tensor_region_demo_source_progress.
