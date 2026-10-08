From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCountedLoop ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceExpressions GuardMemoryPointerAccess
  GuardMemoryRecursiveSource GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorAffineReceipts GuardMemoryMultiTensorAffineFootprint GuardMemoryMultiTensorAffineScan.
From GuardInterface Require Import ClightMultiTensorDataSource ClightMultiTensorDataPackage ClightMultiTensorRegionFactory
  ClightMultiTensorScanAllocation ClightMultiTensorAffinePackageScan.
Import ListNotations.
Local Open Scope Z_scope.

(** Two source loops, three pointers, and different affine access templates.
    Source syntax is independent of the description sent to the checker. *)
Definition affine_scan_a_index := Ebinop Oadd
  (Ebinop Omul (Ebinop Oadd (Etempvar 72%positive type_int32s)
    (Econst_int Int.one type_int32s) type_int32s) (Econst_int (Int.repr 16) type_int32s) type_int32s)
  (Etempvar 73%positive type_int32s) type_int32s.
Definition affine_scan_b_index := Ebinop Oadd
  (Ebinop Omul (Etempvar 72%positive type_int32s) (Econst_int (Int.repr 16) type_int32s) type_int32s)
  (Ebinop Oadd (Etempvar 73%positive type_int32s) (Etempvar 74%positive type_int32s) type_int32s) type_int32s.
Definition affine_scan_c_index := Ebinop Oadd
  (Ebinop Omul (Etempvar 72%positive type_int32s) (Econst_int (Int.repr 16) type_int32s) type_int32s)
  (Etempvar 73%positive type_int32s) type_int32s.
Definition affine_scan_body := Ssequence
  (Sassign (memory_pointer_lvalue 76%positive affine_scan_a_index)
    (Ebinop Oadd (Ebinop Oadd (memory_pointer_lvalue 77%positive affine_scan_b_index)
      (Etempvar 74%positive type_int32s) type_int32s) (Etempvar 75%positive type_int32s) type_int32s))
  (Sassign (memory_pointer_lvalue 78%positive affine_scan_c_index)
    (Ebinop Oadd (memory_pointer_lvalue 76%positive affine_scan_a_index) (Etempvar 75%positive type_int32s) type_int32s)).
Definition affine_scan_inner body := MemorySourceAxis 73%positive 71%positive body (MemorySourceLeaf body).
Definition affine_scan_source_with_body body := memory_nest_source (MemorySourceAxis 72%positive 70%positive
  (Ssequence (rectangle_reset 73%positive) (memory_nest_source (affine_scan_inner body))) (affine_scan_inner body)).
Definition affine_scan_source := affine_scan_source_with_body affine_scan_body.
Definition affine_scan_coordinate_only_body := Ssequence
  (Sassign (memory_pointer_lvalue 76%positive affine_scan_a_index)
    (Ebinop Oadd (memory_pointer_lvalue 77%positive affine_scan_b_index) (Etempvar 75%positive type_int32s) type_int32s))
  (Sassign (memory_pointer_lvalue 78%positive affine_scan_c_index)
    (Ebinop Oadd (memory_pointer_lvalue 76%positive affine_scan_a_index) (Etempvar 75%positive type_int32s) type_int32s)).
Definition affine_scan_a_coordinates :=
  [MemorySourceAdd (MemorySourceTemp 72%positive) (MemorySourceConstant 1);MemorySourceTemp 73%positive].
Definition affine_scan_b_coordinates :=
  [MemorySourceTemp 72%positive;MemorySourceAdd (MemorySourceTemp 73%positive) (MemorySourceTemp 74%positive)].
Definition affine_scan_c_coordinates := map MemorySourceTemp [72%positive;73%positive].
Definition affine_scan_description_with_value value := MultiTensorRegionDescription
  [TensorDimensionConstant 16;TensorDimensionConstant 16] [74%positive;75%positive]
  [MultiTensorAssignmentData (76%positive,affine_scan_a_coordinates) [(77%positive,affine_scan_b_coordinates)]
     value;
   MultiTensorAssignmentData (78%positive,affine_scan_c_coordinates) [(76%positive,affine_scan_a_coordinates)]
     (AddValue (LoadedValue 0) (ParameterValue 3))]
  8 [(1,9);(1,9);(-4,5);(-8,9)].
Definition affine_scan_description := affine_scan_description_with_value
  (AddValue (AddValue (LoadedValue 0) (ParameterValue 2)) (ParameterValue 3)).
Definition affine_scan_checked := check_multi_tensor_region_source affine_scan_source affine_scan_description.
Definition affine_scan_templates := match affine_scan_checked with
  | Some package => multi_tensor_instruction_templates (map mt_instruction (mtr_items package))
  | None => [] end.
Definition affine_scan_pool := map (fun id => (id,type_int32s))
  [72%positive;900%positive;601%positive;602%positive;603%positive;604%positive;605%positive].
Definition affine_scan_slots := match affine_scan_checked with
  | Some package => match multi_tensor_affine_package_allocate package [900%positive] affine_scan_pool with
    | Some allocation => Some (multi_tensor_scan_private allocation) | None => None end
  | None => None end.

Example affine_scan_three_array_source_accepted :
  match affine_scan_checked with Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example affine_scan_coordinate_only_body_matches :
  match describe_multi_tensor_body [TensorDimensionConstant 16;TensorDimensionConstant 16]
    [72%positive;73%positive;74%positive;75%positive] affine_scan_coordinate_only_body
    (mtr_assignments (affine_scan_description_with_value (AddValue (LoadedValue 0) (ParameterValue 3)))) with
  | Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example affine_scan_coordinate_only_parameter_refused :
  match check_multi_tensor_region_source (affine_scan_source_with_body affine_scan_coordinate_only_body)
    (affine_scan_description_with_value (AddValue (LoadedValue 0) (ParameterValue 3))) with
  | Some _ => true | None => false end = false.
Proof. vm_compute; reflexivity. Qed.
Example affine_scan_templates_exact : affine_scan_templates =
  [(76%positive,[([1;0;0;0],1);([0;1;0;0],0)]);
   (77%positive,[([1;0;0;0],0);([0;1;1;0],0)]);
   (78%positive,[([1;0;0;0],0);([0;1;0;0],0)]);
   (76%positive,[([1;0;0;0],1);([0;1;0;0],0)])].
Proof. vm_compute; reflexivity. Qed.
Example affine_scan_typed_resources : affine_scan_slots =
  Some [601%positive;602%positive;603%positive;604%positive;605%positive].
Proof. vm_compute; reflexivity. Qed.
Example affine_scan_pair_count : length (multi_tensor_affine_pairs affine_scan_templates) = 16%nat.
Proof. vm_compute; reflexivity. Qed.
Example affine_scan_shifted_cell : exact_cell (hd (76%positive,[]) affine_scan_templates) [2;3;4;7] =
  {|arr_id:=76%positive;arr_index:=[3;3]|}.
Proof. vm_compute; reflexivity. Qed.
Example affine_scan_parameter_cell : exact_cell (nth 1 affine_scan_templates (77%positive,[])) [2;3;4;7] =
  {|arr_id:=77%positive;arr_index:=[2;7]|}.
Proof. vm_compute; reflexivity. Qed.
Example affine_scan_same_array_no_pointer_test :
  multi_tensor_affine_checked_test [TensorDimensionConstant 16;TensorDimensionConstant 16]
    [601%positive;602%positive;74%positive;75%positive]
    [603%positive;604%positive;74%positive;75%positive]
    ((76%positive,[([1;0;0;0],1);([0;1;0;0],0)]),
     (76%positive,[([1;0;0;0],0);([0;1;0;0],0)])) = Econst_int Int.one type_int32s.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions affine_scan_three_array_source_accepted.
Print Assumptions affine_scan_coordinate_only_body_matches.
Print Assumptions affine_scan_coordinate_only_parameter_refused.
Print Assumptions affine_scan_templates_exact.
Print Assumptions affine_scan_typed_resources.
Print Assumptions affine_scan_pair_count.
Print Assumptions affine_scan_shifted_cell.
Print Assumptions affine_scan_parameter_cell.
Print Assumptions affine_scan_same_array_no_pointer_test.
