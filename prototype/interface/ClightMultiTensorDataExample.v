From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCountedLoop ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceExpressions GuardMemoryPointerAccess
  GuardMemoryRecursiveSource GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import ClightMultiTensorDataSource ClightMultiTensorDataPackage ClightMultiTensorRegionFactory
  ClightMultiTensorScanAllocation.
Import ListNotations.
Local Open Scope Z_scope.

(** Independent actual AST and plain descriptions use identifiers beyond the
    earlier fixed example, with the same two-store flow dependence. *)
Definition multi_tensor_data_index := Ebinop Oadd
  (Ebinop Omul (Ebinop Oadd
    (Ebinop Omul (Etempvar 46%positive type_int32s) (Etempvar 42%positive type_int32s) type_int32s)
    (Etempvar 47%positive type_int32s) type_int32s)
    (Econst_int (Int.repr 5) type_int32s) type_int32s)
  (Etempvar 48%positive type_int32s) type_int32s.
Definition multi_tensor_data_store write read := Sassign (memory_pointer_lvalue write multi_tensor_data_index)
  (Ebinop Oadd (memory_pointer_lvalue read multi_tensor_data_index) (Etempvar 45%positive type_int32s) type_int32s).
Definition multi_tensor_data_body := Ssequence (multi_tensor_data_store 49%positive 50%positive)
  (multi_tensor_data_store 50%positive 49%positive).
Definition multi_tensor_data_inner body := MemorySourceAxis 48%positive 44%positive body (MemorySourceLeaf body).
Definition multi_tensor_data_middle body := MemorySourceAxis 47%positive 43%positive
  (Ssequence (rectangle_reset 48%positive) (memory_nest_source (multi_tensor_data_inner body))) (multi_tensor_data_inner body).
Definition multi_tensor_data_source_with_body body := memory_nest_source (MemorySourceAxis 46%positive 41%positive
  (Ssequence (rectangle_reset 47%positive) (memory_nest_source (multi_tensor_data_middle body))) (multi_tensor_data_middle body)).
Definition multi_tensor_data_source := multi_tensor_data_source_with_body multi_tensor_data_body.
Definition multi_tensor_data_coordinates := map MemorySourceTemp [46%positive;47%positive;48%positive].
Definition multi_tensor_data_assignment write read := MultiTensorAssignmentData (write,multi_tensor_data_coordinates)
  [(read,multi_tensor_data_coordinates)] (AddValue (LoadedValue 0) (ParameterValue 4)).
Definition multi_tensor_data_assignments := [multi_tensor_data_assignment 49%positive 50%positive;
  multi_tensor_data_assignment 50%positive 49%positive].
Definition multi_tensor_data_profile :=
  [(1,33);(1,33);(1,6);(1,1000);(Int.min_signed,Int.max_signed+1);(1,33);(1,1000)].
Definition multi_tensor_data_description assignments scalars := MultiTensorRegionDescription
  [TensorDimensionTemp 41%positive;TensorDimensionTemp 42%positive;TensorDimensionConstant 5]
  scalars assignments 32 multi_tensor_data_profile.
Definition multi_tensor_data_accepted source assignments scalars :=
  match check_multi_tensor_region_source source (multi_tensor_data_description assignments scalars) with
  | Some _ => true | None => false end.

Example multi_tensor_data_renamed_source_accepted :
  multi_tensor_data_accepted multi_tensor_data_source multi_tensor_data_assignments [42%positive;45%positive] = true.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_data_body_skips_accepted : multi_tensor_data_accepted
  (multi_tensor_data_source_with_body (Ssequence Sskip (Ssequence multi_tensor_data_body Sskip)))
  multi_tensor_data_assignments [42%positive;45%positive] = true.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_data_outer_wrapper_progress_refused : multi_tensor_data_accepted
  (Ssequence Sskip (Ssequence multi_tensor_data_source Sskip)) multi_tensor_data_assignments [42%positive;45%positive] = false.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_data_pointer_mismatch_refused : multi_tensor_data_accepted multi_tensor_data_source
  [multi_tensor_data_assignment 49%positive 51%positive;multi_tensor_data_assignment 50%positive 49%positive]
  [42%positive;45%positive] = false.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_data_missing_statement_refused : multi_tensor_data_accepted multi_tensor_data_source
  [multi_tensor_data_assignment 49%positive 50%positive] [42%positive;45%positive] = false.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_data_unused_scalar_refused : multi_tensor_data_accepted multi_tensor_data_source
  multi_tensor_data_assignments [42%positive;45%positive;57%positive] = false.
Proof. vm_compute; reflexivity. Qed.

Definition multi_tensor_data_private_pool :=
  [(46%positive,type_int32s);(301%positive,type_int32s);(401%positive,Tpointer type_int32s noattr)] ++
  map (fun identifier => (identifier,type_int32s))
    [501%positive;502%positive;503%positive;504%positive;505%positive;506%positive;507%positive;508%positive].
Definition multi_tensor_data_scan_slots pool :=
  match allocate_multi_tensor_scan multi_tensor_data_source [301%positive] pool 3 with
  | Some allocation => Some (multi_tensor_scan_private allocation)
  | None => None end.
Example multi_tensor_data_typed_fresh_allocation : multi_tensor_data_scan_slots multi_tensor_data_private_pool =
  Some [501%positive;502%positive;503%positive;504%positive;505%positive;506%positive;507%positive].
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_data_exhausted_pool_refused : multi_tensor_data_scan_slots
  [(46%positive,type_int32s);(301%positive,type_int32s);(401%positive,Tpointer type_int32s noattr)] = None.
Proof. vm_compute; reflexivity. Qed.
Example multi_tensor_data_duplicate_slots_refused : multi_tensor_data_scan_slots
  (map (fun identifier => (identifier,type_int32s))
    [501%positive;501%positive;503%positive;504%positive;505%positive;506%positive;507%positive]) = None.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions multi_tensor_data_renamed_source_accepted.
Print Assumptions multi_tensor_data_body_skips_accepted.
Print Assumptions multi_tensor_data_outer_wrapper_progress_refused.
Print Assumptions multi_tensor_data_pointer_mismatch_refused.
Print Assumptions multi_tensor_data_missing_statement_refused.
Print Assumptions multi_tensor_data_unused_scalar_refused.
Print Assumptions multi_tensor_data_typed_fresh_allocation.
Print Assumptions multi_tensor_data_exhausted_pool_refused.
Print Assumptions multi_tensor_data_duplicate_slots_refused.
