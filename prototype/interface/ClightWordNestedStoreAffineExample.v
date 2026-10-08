From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop
  ClightSyntaxEquality ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceExpressions
  GuardMemoryDynamicTensorBackend GuardMemoryPointerAccess.
From GuardInterface Require Import ClightWordStoreSequenceExample ClightWordStoreSequenceScanExample
  ClightWordStoreNestedGuard ClightWordStoreNestedGuardExample ClightWordNestedStoreFactory
  ClightWordNestedStoreDataEntry ClightWordNestedStoreFactoryExample ClightWordNestedStoreAffine
  ClightNestedExpressionTransport ClightSignedExpressionProgress ClightStrictLoopProgress
  ClightSharedGuard ClightMultiTensorDataSource ClightMultiTensorDataPackage ClightDualLoadedUnitSyntax
  ClightExpressionHeaderCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition nested_affine_pool := map (fun id=>(id,type_int32s))
  ([2;4;20;21;22;23;100]%positive++map Pos.of_nat (seq 201 64)).
Definition nested_affine_empty_package_check := check_word_nested_store_data_polyhedral_source
  (nws_source nested_factory_model_description) nested_guard_demo_public nested_affine_pool
  nested_factory_model_description (fun _=>Some nested_factory_model_data).

Example nested_affine_empty_model_checked :
  match nested_affine_empty_package_check with Some _=>true|None=>false end=true.
Proof. vm_compute; reflexivity. Qed.
Lemma nested_affine_empty_package_exists : exists package, nested_affine_empty_package_check=Some package.
Proof.
  pose proof nested_affine_empty_model_checked as CHECK.
  destruct nested_affine_empty_package_check as [package|];
    [exists package; reflexivity|discriminate].
Qed.
Lemma nested_affine_empty_package_shape package : nested_affine_empty_package_check=Some package ->
  nwsp_guard_code (nwspp_header package)=nested_guard_demo_code (Int.repr 3) /\
  nwa_cache (nwsp_allocation (nwspp_header package))=2%positive /\
  nwa_flag (nwsp_allocation (nwspp_header package))=100%positive /\
  nws_cached (nwsp_allocation (nwspp_header package))=
    nested_cached_source 1%positive 2%positive 3%positive 4%positive nested_factory_model_body.
Proof.
  intro CHECK.
  assert (SHAPE : match nested_affine_empty_package_check with
    | Some p =>
      if statement_eq (nwsp_guard_code (nwspp_header p)) (nested_guard_demo_code (Int.repr 3)) then
      if peq (nwa_cache (nwsp_allocation (nwspp_header p))) 2%positive then
      if peq (nwa_flag (nwsp_allocation (nwspp_header p))) 100%positive then
      if statement_eq (nws_cached (nwsp_allocation (nwspp_header p)))
        (nested_cached_source 1%positive 2%positive 3%positive 4%positive nested_factory_model_body)
        then true else false else false else false else false
    | None => false end = true) by (vm_compute; reflexivity).
  rewrite CHECK in SHAPE.
  change ((if statement_eq (nwsp_guard_code (nwspp_header package)) (nested_guard_demo_code (Int.repr 3)) then
      if peq (nwa_cache (nwsp_allocation (nwspp_header package))) 2%positive then
      if peq (nwa_flag (nwsp_allocation (nwspp_header package))) 100%positive then
      if statement_eq (nws_cached (nwsp_allocation (nwspp_header package)))
        (nested_cached_source 1%positive 2%positive 3%positive 4%positive nested_factory_model_body)
        then true else false else false else false else false) = true) in SHAPE.
  destruct (statement_eq (nwsp_guard_code (nwspp_header package))
    (nested_guard_demo_code (Int.repr 3))) as [CODE|]; [|discriminate].
  destruct (peq (nwa_cache (nwsp_allocation (nwspp_header package))) 2%positive)
    as [CACHE|]; [|discriminate].
  destruct (peq (nwa_flag (nwsp_allocation (nwspp_header package))) 100%positive)
    as [FLAG|]; [|discriminate].
  destruct (statement_eq (nws_cached (nwsp_allocation (nwspp_header package)))
    (nested_cached_source 1%positive 2%positive 3%positive 4%positive nested_factory_model_body))
    as [CACHED|]; [|discriminate].
  repeat split; assumption.
Qed.

(** An arbitrary candidate, including one that cannot terminate, is unreachable
    on the accepted empty path.  No child/array parameter is initialized. *)
Theorem nested_affine_empty_bypasses_candidate fe ge locals candidate :
  exists package after, nested_affine_empty_package_check=Some package /\
    exec_stmt fe ge locals nested_guard_demo_empty_temps sequence_scan_empty_memory
      (nwspp_affine_target package candidate) E0 after sequence_scan_empty_memory Out_normal /\
    temp_agree nested_guard_demo_public nested_guard_demo_empty_temps after /\
    after!12%positive=None /\ after!4%positive=None /\ after!9%positive=None /\ after!10%positive=None.
Proof.
  destruct nested_affine_empty_package_exists as [package CHECK].
  destruct (nested_affine_empty_package_shape CHECK) as [CODE [CACHE [FLAG CACHED]]].
  set (captured:=PTree.set 2%positive (Vint Int.zero) nested_guard_demo_empty_temps).
  set (after:=PTree.set 100%positive (Vint Int.one) captured).
  destruct (nested_guard_demo_empty_guard fe ge locals (Int.repr 3))
    as [GUARD [CHILD_NONE [CACHE_NONE [A_NONE [B_NONE FLAG_WORD]]]]].
  change (exec_stmt fe ge locals nested_guard_demo_empty_temps sequence_scan_empty_memory
    (nested_guard_demo_code (Int.repr 3)) E0 after sequence_scan_empty_memory Out_normal) in GUARD.
  exists package,after; split; [exact CHECK|split].
  - unfold nwspp_affine_target; rewrite CODE,CACHE,FLAG,CACHED.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact GUARD|].
    eapply word_store_if_test_execution with (accepted:=true).
    + apply shared_guard_choice_test; exact FLAG_WORD.
    + eapply word_store_if_test_execution with (accepted:=false).
      * change false with (Int.lt Int.zero Int.zero); apply word_store_positive_test_execution; reflexivity.
      * unfold nested_cached_source,frontend_counted_loop; apply strict_zero_trip_encode.
        change false with (Int.lt Int.zero Int.zero); eapply signed_expression_test_eval;
          [reflexivity|reflexivity|constructor; reflexivity].
  - split.
    + unfold after,captured; eapply temp_agree_trans; apply temp_agree_set;
        unfold nested_guard_demo_public; cbn; intuition congruence.
    + repeat split; assumption.
Qed.

(** A real 2D affine layout and two statements with a flow dependence at each
    cell. Loaded bounds are separate from the constant physical stride. *)
Definition nested_affine_index := Ebinop Oadd
  (Ebinop Omul (Etempvar 1%positive type_int32s) (Econst_int (Int.repr 16) type_int32s) type_int32s)
  (Etempvar 3%positive type_int32s) type_int32s.
Definition nested_affine_store write read := Sassign (memory_pointer_lvalue write nested_affine_index)
  (Ebinop Oadd (memory_pointer_lvalue read nested_affine_index)
    (Econst_int (Int.repr 3) type_int32s) type_int32s).
Definition nested_affine_body := Ssequence (nested_affine_store 9%positive 10%positive)
  (nested_affine_store 10%positive 9%positive).
Definition nested_affine_description := WordNestedStoreDescription
  1%positive 11%positive Int.zero 3%positive 12%positive Int.zero nested_affine_body.
Definition nested_affine_assignment write read := MultiTensorAssignmentData
  (write,map MemorySourceTemp [1;3]%positive) [(read,map MemorySourceTemp [1;3]%positive)]
  (AddValue (LoadedValue 0) (ConstantValue 3)).
Definition nested_affine_model_data := MultiTensorRegionDescription
  [TensorDimensionConstant 16;TensorDimensionConstant 16] []
  [nested_affine_assignment 9%positive 10%positive;nested_affine_assignment 10%positive 9%positive]
  4 [(1,5);(1,5)].
Example nested_affine_two_array_source_model_checked :
  match check_word_nested_store_data_polyhedral_source (nws_source nested_affine_description)
    nested_guard_demo_public nested_affine_pool nested_affine_description
    (fun _=>Some nested_affine_model_data) with Some _=>true|None=>false end=true.
Proof. vm_compute; reflexivity. Qed.
Example nested_affine_wrong_flow_description_refused :
  match check_word_nested_store_data_polyhedral_source (nws_source nested_affine_description)
    nested_guard_demo_public nested_affine_pool nested_affine_description
    (fun _=>Some (MultiTensorRegionDescription [TensorDimensionConstant 16;TensorDimensionConstant 16] []
      [nested_affine_assignment 9%positive 10%positive;nested_affine_assignment 10%positive 12%positive]
      4 [(1,5);(1,5)])) with Some _=>false|None=>true end=true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions nested_affine_empty_model_checked.
Print Assumptions nested_affine_empty_package_exists.
Print Assumptions nested_affine_empty_package_shape.
Print Assumptions nested_affine_empty_bypasses_candidate.
Print Assumptions nested_affine_two_array_source_model_checked.
Print Assumptions nested_affine_wrong_flow_description_refused.
