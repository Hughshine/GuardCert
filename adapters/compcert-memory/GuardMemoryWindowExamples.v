From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightCountedLoop ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceExpressions GuardMemoryNaryAffineAccess
  GuardMemoryNaryCompute GuardMemoryPointerCompute GuardMemoryRecursiveSource.
From GuardMemory Require Import GuardMemoryWindowPackageBuilder GuardMemoryWindowPackage GuardMemoryWindowStartedPackage.
Import ListNotations.
Local Open Scope Z_scope.
Definition window_example_access := MemoryNaryAccess 4%positive (RectangleShape 16 1 1 0)
  (MemorySourceAdd (MemorySourceTemp 1%positive) (MemorySourceTemp 3%positive)) ([1;1],0).
Definition window_example_operation := MemoryNaryCompute window_example_access [] (ParameterValue 2)
  (Etempvar 5%positive type_int32s).
Definition window_example_body := memory_pointer_compute_statement window_example_operation.
Definition window_example_nest := MemorySourceAxis 1%positive 2%positive window_example_body (MemorySourceLeaf window_example_body).
Definition window_example_source := memory_nest_source window_example_nest.
Definition window_example_checked low high :=
  make_window_region_package window_example_source window_example_nest [4] (-2)
    [3%positive] [(-2,3)] [4%positive] low high [5%positive] [window_example_operation].
Definition window_example_accept low high := match window_example_checked low high with Some _ => true | None => false end.
Example window_negative_root_parameter_and_index : window_example_accept (-16) 16 = true.
Proof. vm_compute; reflexivity. Qed.
Example window_zero_based_registry_rejects_negative_index : window_example_accept 0 16 = false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions window_negative_root_parameter_and_index.
