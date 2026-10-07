From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryNaryCompute
  GuardMemoryNaryAffineAccess GuardMemoryPointerCompute GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage.
From GuardInterface Require Import CompCertInvariantWordObservation ClightNestedInvariantWordCheck
  ClightNestedInvariantStability ClightNestedConstantWordExample ClightNestedConstantNumericExample
  ClightNestedConstantModel ClightConstantBoundModel ClightNestedConstantSite.
Import ListNotations.
Local Open Scope Z_scope.

Definition niw_expression := MemorySourceAdd
  (MemorySourceAdd (MemorySourceTemp 12%positive) (MemorySourceTemp 13%positive))
  (MemorySourceConstant 1).
Definition niw_access := MemoryNaryAccess 10%positive (RectangleShape 5120 1 1 0)
  ncn_address ([80;5;1;0;0;0;0],0).
Definition niw_operation := MemoryNaryCompute niw_access []
  (AddValue (AddValue (ParameterValue 5) (ParameterValue 6)) (ConstantValue 1))
  (memory_source_affine_code niw_expression).
Definition niw_leaf := memory_pointer_compute_statement niw_operation.
Definition niw_shape := NestedConstantShape 1%positive 2%positive 3%positive
  4%positive 5%positive 51%positive 50%positive 5 niw_leaf 11%positive Int.one Int.one Int.one.
Definition niw_parameters := [4%positive;5%positive;12%positive;13%positive].
Definition niw_live := ncw_indexed_live++[12%positive;13%positive].
Definition niw_body := cached_child_model 2%positive 5%positive 51%positive
  (constant_affine_body_model 3%positive 50%positive 5 niw_leaf).
Definition niw_child := AffineSourceAxis 2%positive 51%positive (MemorySourceTemp 5%positive)
  (constant_affine_body_model 3%positive 50%positive 5 niw_leaf)
  (AffineSourceAxis 3%positive 50%positive (MemorySourceConstant 5) niw_leaf (AffineSourceLeaf niw_leaf)).
Definition niw_proposal := AffineGuardProposal 1%positive 4%positive niw_body niw_child
  [(0,16);(0,16);(0,5);(0,16);(0,16);(Int.min_signed,Int.max_signed+1);(Int.min_signed,Int.max_signed+1)]
  0 1280 [10%positive] [niw_operation]
  [(0,16);(0,16);(Int.min_signed,Int.max_signed+1);(Int.min_signed,Int.max_signed+1)]
  0 16 [(0,16);(0,5)]
  [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive] 107%positive.

Example niw_actual_source_package_checked :
  match check_nested_constant_site (ncs_original niw_shape) niw_parameters niw_live niw_proposal niw_shape
    with Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example niw_value_selected :
  ncs_invariant_expression niw_parameters niw_shape = Some niw_expression.
Proof. vm_compute; reflexivity. Qed.
Example niw_literal_lowering_preserved :
  ncs_invariant_stability_code ncw_indexed_parameters ncw_indexed_shape ncw_indexed_proposal =
    ClightNestedConstantStability.ncs_stability_code ncw_indexed_shape ncw_indexed_proposal.
Proof. vm_compute; reflexivity. Qed.
Example niw_unlisted_parameter_refused :
  ncs_invariant_expression [4%positive;5%positive;12%positive] niw_shape = None.
Proof. vm_compute; reflexivity. Qed.
Example niw_coordinate_value_refused :
  ncs_invariant_expression niw_parameters (NestedConstantShape 1%positive 2%positive 3%positive
    4%positive 5%positive 51%positive 50%positive 5 ncn_leaf 11%positive Int.one Int.one Int.one) = None.
Proof. vm_compute; reflexivity. Qed.
Example niw_parameter_update_refused :
  check_invariant_word_control niw_expression
    (Ssequence niw_leaf (Sset 12%positive (Econst_int Int.zero type_int32s))) = false.
Proof. vm_compute; reflexivity. Qed.
Example niw_mixed_store_value_refused :
  check_invariant_word_control niw_expression
    (Ssequence niw_leaf ncw_indexed_leaf) = false.
Proof. vm_compute; reflexivity. Qed.
Example niw_partial_store_refused :
  check_invariant_word_control niw_expression
    (Sassign (Ederef (Etempvar 10%positive (Tpointer type_int32s noattr)) (Tint I16 Signed noattr))
      (memory_source_affine_code niw_expression)) = false.
Proof. vm_compute; reflexivity. Qed.

Definition niw_wrap_temps := PTree.set 12%positive (Vint (Int.repr Int.min_signed))
  (PTree.set 13%positive (Vint (Int.repr Int.min_signed)) (ncw_temps 2 2)).
Example niw_wrapped_value_is_one : ncs_invariant_word niw_expression niw_wrap_temps = Int.one.
Proof. apply Int.same_if_eq; vm_compute; reflexivity. Qed.
Theorem niw_actual_modular_comparison ge locals memory :
  expression_test (ncs_invariant_pair_expression niw_shape niw_expression)
    (Entry ge locals niw_wrap_temps memory) true.
Proof.
  change (expression_test (ncs_invariant_pair_expression niw_shape niw_expression)
    (Entry ge locals niw_wrap_temps memory)
    (ClightNestedConstantWordModel.ncs_same_word_flag niw_shape Int.one (Entry ge locals niw_wrap_temps memory))).
  apply ncs_invariant_pair_expression_test with (root:=Int.repr 2) (child:=Int.repr 2).
  - reflexivity.
  - reflexivity.
  - rewrite <-niw_wrapped_value_is_one; apply memory_source_affine_evaluation.
    intros identifier MEMBER.
    cbn [niw_expression memory_source_affine_reads app List.In] in MEMBER.
    destruct MEMBER as [<-|[<-|[]]]; vm_compute; reflexivity.
Qed.

Print Assumptions niw_actual_source_package_checked.
Print Assumptions niw_value_selected.
Print Assumptions niw_literal_lowering_preserved.
Print Assumptions niw_unlisted_parameter_refused.
Print Assumptions niw_coordinate_value_refused.
Print Assumptions niw_parameter_update_refused.
Print Assumptions niw_mixed_store_value_refused.
Print Assumptions niw_partial_store_refused.
Print Assumptions niw_wrapped_value_is_one.
Print Assumptions niw_actual_modular_comparison.
