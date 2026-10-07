From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryNaryCompute
  GuardMemoryNaryAffineAccess GuardMemoryPointerCompute GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage.
From GuardInterface Require Import CompCertWordObservation ClightWordObservationControl
  ClightNestedConstantSite ClightNestedConstantWordModel ClightNestedConstantWordCheck
  ClightNestedConstantNumericExample ClightConstantBoundModel ClightNestedConstantModel.
Import ListNotations.

Definition ncw_leaf := Sassign (Ederef (Etempvar 10%positive (Tpointer type_int32s noattr)) type_int32s)
  (Econst_int Int.one type_int32s).
Definition ncw_shape := NestedConstantShape 1%positive 2%positive 3%positive
  4%positive 5%positive 51%positive 50%positive 5 ncw_leaf 11%positive Int.one Int.one Int.one.
Definition ncw_temps root child := PTree.set 4%positive (Vint (Int.repr root))
  (PTree.set 5%positive (Vint (Int.repr child)) (PTree.empty val)).

(** A real indexed BODY checked by the existing source/model package,
    rather than an assumed site with an unrelated constant-store body. *)
Definition ncw_indexed_access := MemoryNaryAccess 10%positive (RectangleShape 5120 1 1 0)
  ncn_address ([80;5;1;0;0],0).
Definition ncw_indexed_operation := MemoryNaryCompute ncw_indexed_access [] (ConstantValue 1)
  (Econst_int Int.one type_int32s).
Definition ncw_indexed_leaf := memory_pointer_compute_statement ncw_indexed_operation.
Definition ncw_indexed_shape := NestedConstantShape 1%positive 2%positive 3%positive
  4%positive 5%positive 51%positive 50%positive 5 ncw_indexed_leaf 11%positive Int.one Int.one Int.one.
Definition ncw_indexed_body := cached_child_model 2%positive 5%positive 51%positive
  (constant_affine_body_model 3%positive 50%positive 5 ncw_indexed_leaf).
Definition ncw_indexed_child := AffineSourceAxis 2%positive 51%positive (MemorySourceTemp 5%positive)
  (constant_affine_body_model 3%positive 50%positive 5 ncw_indexed_leaf)
  (AffineSourceAxis 3%positive 50%positive (MemorySourceConstant 5) ncw_indexed_leaf (AffineSourceLeaf ncw_indexed_leaf)).
Definition ncw_indexed_proposal := AffineGuardProposal 1%positive 4%positive ncw_indexed_body ncw_indexed_child
  [(0,16);(0,16);(0,5);(0,16);(0,16)] 0 1280 [10%positive] [ncw_indexed_operation]
  [(0,16);(0,16)] 0 16 [(0,16);(0,5)]
  [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive] 107%positive.
Definition ncw_indexed_parameters := [4%positive;5%positive].
Definition ncw_indexed_live := [1%positive;2%positive;3%positive;10%positive;11%positive].

Example ncw_indexed_constant_site_checked :
  match check_nested_constant_site (ncs_original ncw_indexed_shape) ncw_indexed_parameters
    ncw_indexed_live ncw_indexed_proposal ncw_indexed_shape with Some _ => true | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example ncw_indexed_body_same_word_checked :
  check_constant_word_statement Int.one ncw_indexed_leaf = true.
Proof. vm_compute; reflexivity. Qed.

Example ncw_original_three_axis_syntax_is_classified :
  check_constant_word_control Int.one (ncs_original ncw_shape) = true.
Proof. vm_compute; reflexivity. Qed.

Example ncw_same_word_accepts ge locals memory :
  ncs_same_word_flag ncw_shape Int.one (Entry ge locals (ncw_temps 2 2) memory) = true.
Proof. vm_compute; reflexivity. Qed.

Example ncw_changed_root_refused ge locals memory :
  ncs_same_word_flag ncw_shape Int.one (Entry ge locals (ncw_temps 3 2) memory) = false.
Proof. vm_compute; reflexivity. Qed.

Example ncw_changed_child_refused ge locals memory :
  ncs_same_word_flag ncw_shape Int.one (Entry ge locals (ncw_temps 2 3) memory) = false.
Proof. vm_compute; reflexivity. Qed.

Theorem ncw_actual_accepting_check fe ge locals memory :
  exec_stmt fe ge locals (ncw_temps 2 2) memory (ncs_same_word_check ncw_shape Int.one 107%positive)
    E0 (PTree.set 107%positive (Vint Int.one) (ncw_temps 2 2)) memory Out_normal.
Proof. apply ncs_same_word_check_execution with (root:=Int.repr 2) (child:=Int.repr 2); reflexivity. Qed.

(** An unsuccessful first comparison does not read an undefined child cache. *)
Theorem ncw_actual_root_refusal_skips_child fe ge locals memory :
  let temps := PTree.set 4%positive (Vint (Int.repr 3)) (PTree.empty val) in
  exec_stmt fe ge locals temps memory (ncs_same_word_check ncw_shape Int.one 107%positive)
    E0 (PTree.set 107%positive (Vint Int.zero) temps) memory Out_normal.
Proof.
  cbn zeta; unfold ncs_same_word_check.
  eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
  - eapply eval_Ebinop; [constructor; reflexivity|constructor|reflexivity].
  - reflexivity.
  - constructor; constructor.
Qed.

Example ncw_different_store_word_not_classified :
  check_constant_word_control Int.zero (ncs_original ncw_shape) = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions ncw_original_three_axis_syntax_is_classified.
Print Assumptions ncw_indexed_constant_site_checked.
Print Assumptions ncw_indexed_body_same_word_checked.
Print Assumptions ncw_same_word_accepts.
Print Assumptions ncw_changed_root_refused.
Print Assumptions ncw_changed_child_refused.
Print Assumptions ncw_actual_accepting_check.
Print Assumptions ncw_actual_root_refusal_skips_child.
Print Assumptions ncw_different_store_word_not_classified.
