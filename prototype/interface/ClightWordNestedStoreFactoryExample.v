From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceExpressions
  GuardMemoryDynamicTensorBackend GuardMemoryPointerAccess.
From GuardInterface Require Import ClightWordStoreSequenceExample ClightWordStoreSequenceScanExample
  ClightWordStoreNestedScanExample ClightWordStoreNestedGuardExample
  ClightWordNestedStoreFactory ClightWordNestedStoreDataEntry ClightMultiTensorDataSource ClightMultiTensorDataPackage.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition nested_factory_description delta := WordNestedStoreDescription
  1%positive 11%positive Int.zero 3%positive 12%positive Int.zero (sequence_demo_body delta).
Definition nested_factory_pool :=
  [(1%positive,type_int32s);(11%positive,Tpointer type_int32s noattr)] ++
  map (fun id=>(id,type_int32s)) [2;4;20;21;22;23;100;201;202;203;204;205;206;207]%positive.
Definition nested_factory_check delta := check_word_nested_store_data_source (nested_scan_demo_source delta)
  nested_guard_demo_public nested_factory_pool (nested_factory_description delta).
Definition nested_factory_accepted delta := match nested_factory_check delta with Some _=>true|None=>false end.

Example nested_factory_actual_source_checked : nested_factory_accepted (Int.repr 3)=true.
Proof. vm_compute; reflexivity. Qed.
Example nested_factory_alias_source_checked : nested_factory_accepted (Int.repr (-2))=true.
Proof. vm_compute; reflexivity. Qed.
Example nested_factory_slots_computed :
  match allocate_word_nested_store (nested_scan_demo_source (Int.repr 3)) nested_guard_demo_public nested_factory_pool with
  | Some a=>Some (nwa_private a)|None=>None end=Some [2;4;20;21;22;23;100]%positive.
Proof. vm_compute; reflexivity. Qed.
Example nested_factory_exhausted_pool_refuses :
  match check_word_nested_store_data_source (nested_scan_demo_source (Int.repr 3)) nested_guard_demo_public
    (map (fun id=>(id,type_int32s)) [2;4;20;21;22;23]%positive) (nested_factory_description (Int.repr 3)) with
  | Some _=>false|None=>true end=true.
Proof. vm_compute; reflexivity. Qed.
Example nested_factory_duplicate_slots_refuse :
  match check_word_nested_store_data_source (nested_scan_demo_source (Int.repr 3)) nested_guard_demo_public
    (map (fun id=>(id,type_int32s)) [2;4;20;21;22;23;23]%positive) (nested_factory_description (Int.repr 3)) with
  | Some _=>false|None=>true end=true.
Proof. vm_compute; reflexivity. Qed.
Example nested_factory_wrong_actual_AST_refuses :
  match check_word_nested_store_data_source Sskip nested_guard_demo_public nested_factory_pool
    (nested_factory_description (Int.repr 3)) with Some _=>false|None=>true end=true.
Proof. vm_compute; reflexivity. Qed.
Example nested_factory_public_collision_refuses :
  match check_word_nested_store_data_source (nested_scan_demo_source (Int.repr 3)) (2%positive::nested_guard_demo_public)
    (map (fun id=>(id,type_int32s)) [2;4;20;21;22;23;100]%positive) (nested_factory_description (Int.repr 3)) with
  | Some _=>false|None=>true end=true.
Proof. vm_compute; reflexivity. Qed.

Lemma nested_factory_checked_exists delta : nested_factory_accepted delta=true ->
  exists package, nested_factory_check delta=Some package.
Proof.
  unfold nested_factory_accepted; destruct (nested_factory_check delta) as [package|] eqn:CHECK;
    [intro; exists package; reflexivity|discriminate].
Qed.
Theorem nested_factory_accepting_execution fe ge locals :
  exists package after, nested_factory_check (Int.repr 3)=Some package /\
    exec_stmt fe ge locals (nested_scan_demo_temps 0 Int.one) sequence_demo_memory (nwsp_rewrite package)
      E0 after sequence_demo_final Out_normal /\
    temp_agree nested_guard_demo_public (nested_scan_demo_exit (nested_scan_demo_temps 0 Int.one)) after.
Proof.
  destruct (nested_factory_checked_exists (Int.repr 3) nested_factory_actual_source_checked) as [package CHECK].
  destruct (@nwsp_rewrite_execution _ _ _ package fe ge locals (nested_scan_demo_temps 0 Int.one)
    sequence_demo_memory (nested_scan_demo_exit (nested_scan_demo_temps 0 Int.one)) sequence_demo_final
    (nested_scan_demo_original_accepts fe ge locals)) as [after [RUN PUBLIC]].
  exists package,after; repeat split; assumption.
Qed.
Theorem nested_factory_child_fallback_execution fe ge locals :
  exists package after, nested_factory_check (Int.repr (-2))=Some package /\
    exec_stmt fe ge locals (nested_scan_demo_temps 8 (Int.repr 2)) nested_scan_demo_alias_memory (nwsp_rewrite package)
      E0 after nested_scan_demo_alias_final Out_normal /\
    temp_agree nested_guard_demo_public (nested_scan_demo_exit (nested_scan_demo_temps 8 (Int.repr 2))) after.
Proof.
  destruct (nested_factory_checked_exists (Int.repr (-2)) nested_factory_alias_source_checked) as [package CHECK].
  destruct (@nwsp_rewrite_execution _ _ _ package fe ge locals (nested_scan_demo_temps 8 (Int.repr 2))
    nested_scan_demo_alias_memory (nested_scan_demo_exit (nested_scan_demo_temps 8 (Int.repr 2))) nested_scan_demo_alias_final
    (nested_scan_demo_original_child_alias fe ge locals)) as [after [RUN PUBLIC]].
  exists package,after; repeat split; assumption.
Qed.
Theorem nested_factory_empty_execution fe ge locals :
  exists package after, nested_factory_check (Int.repr 3)=Some package /\
    exec_stmt fe ge locals nested_guard_demo_empty_temps sequence_scan_empty_memory (nwsp_rewrite package)
      E0 after sequence_scan_empty_memory Out_normal /\
    temp_agree nested_guard_demo_public nested_guard_demo_empty_temps after.
Proof.
  destruct (nested_factory_checked_exists (Int.repr 3) nested_factory_actual_source_checked) as [package CHECK].
  destruct (@nwsp_rewrite_execution _ _ _ package fe ge locals nested_guard_demo_empty_temps
    sequence_scan_empty_memory nested_guard_demo_empty_temps sequence_scan_empty_memory
    (nested_guard_demo_empty_original fe ge locals (Int.repr 3))) as [after [RUN PUBLIC]].
  exists package,after; repeat split; assumption.
Qed.

(** Independent source AST and ordinary metadata for an actual two-store
    cached model.  The callback returns data, not semantic evidence. *)
Definition nested_factory_model_zero := Econst_int Int.zero type_int32s.
Definition nested_factory_model_store write read := Sassign
  (memory_pointer_lvalue write nested_factory_model_zero)
  (Ebinop Oadd (memory_pointer_lvalue read nested_factory_model_zero)
    (Econst_int (Int.repr 3) type_int32s) type_int32s).
Definition nested_factory_model_body := Ssequence (nested_factory_model_store 9%positive 10%positive)
  (nested_factory_model_store 10%positive 9%positive).
Definition nested_factory_model_description := WordNestedStoreDescription
  1%positive 11%positive Int.zero 3%positive 12%positive Int.zero nested_factory_model_body.
Definition nested_factory_model_data := MultiTensorRegionDescription [TensorDimensionConstant 1] []
  [MultiTensorAssignmentData (9%positive,[MemorySourceConstant 0]) [(10%positive,[MemorySourceConstant 0])]
     (AddValue (LoadedValue 0) (ConstantValue 3));
   MultiTensorAssignmentData (10%positive,[MemorySourceConstant 0]) [(9%positive,[MemorySourceConstant 0])]
     (AddValue (LoadedValue 0) (ConstantValue 3))] 4 [(1,5);(1,5)].
Example nested_factory_polyhedral_model_checked :
  match check_word_nested_store_data_polyhedral_source (nws_source nested_factory_model_description)
    nested_guard_demo_public nested_factory_pool nested_factory_model_description
    (fun _=>Some nested_factory_model_data) with Some _=>true|None=>false end=true.
Proof. vm_compute; reflexivity. Qed.
Example nested_factory_model_mismatch_refuses :
  match check_word_nested_store_data_polyhedral_source (nested_scan_demo_source (Int.repr 3))
    nested_guard_demo_public nested_factory_pool (nested_factory_description (Int.repr 3))
    (fun _=>Some nested_factory_model_data) with Some _=>false|None=>true end=true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions nested_factory_actual_source_checked.
Print Assumptions nested_factory_alias_source_checked.
Print Assumptions nested_factory_slots_computed.
Print Assumptions nested_factory_exhausted_pool_refuses.
Print Assumptions nested_factory_duplicate_slots_refuse.
Print Assumptions nested_factory_wrong_actual_AST_refuses.
Print Assumptions nested_factory_public_collision_refuses.
Print Assumptions nested_factory_checked_exists.
Print Assumptions nested_factory_accepting_execution.
Print Assumptions nested_factory_child_fallback_execution.
Print Assumptions nested_factory_empty_execution.
Print Assumptions nested_factory_polyhedral_model_checked.
Print Assumptions nested_factory_model_mismatch_refuses.
