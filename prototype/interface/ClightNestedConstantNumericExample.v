From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightRectangularGuard ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryPointerCompute GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestPackageGuard.
From GuardInterface Require Import ClightConstantBoundModel ClightNestedConstantModel ClightNestedConstantNumericGuard.
Import ListNotations.
Local Open Scope Z_scope.

(** A checked three-axis numeric package, with a BODY-only parameter in
    addition to the two captured header words. This is not a new compiler. *)
Definition ncn_address := MemorySourceAdd
  (MemorySourceScale 5(MemorySourceAdd(MemorySourceScale 16(MemorySourceTemp 1%positive))
    (MemorySourceTemp 2%positive)))(MemorySourceTemp 3%positive).
Definition ncn_value := MemorySourceAdd
  (MemorySourceAdd(MemorySourceTemp 1%positive)(MemorySourceTemp 2%positive))
  (MemorySourceAdd(MemorySourceTemp 3%positive)(MemorySourceTemp 7%positive)).
Definition ncn_access := MemoryNaryAccess 10%positive(RectangleShape 5120 1 1 0)
  ncn_address([80;5;1;0;0;0],0).
Definition ncn_operation := MemoryNaryCompute ncn_access []
  (AddValue(AddValue(ParameterValue 0)(ParameterValue 1))
    (AddValue(ParameterValue 2)(ParameterValue 5)))(memory_source_affine_code ncn_value).
Definition ncn_leaf := memory_pointer_compute_statement ncn_operation.
Definition ncn_body := cached_child_model 2%positive 5%positive 51%positive
  (constant_affine_body_model 3%positive 50%positive 5 ncn_leaf).
Definition ncn_child := AffineSourceAxis 2%positive 51%positive(MemorySourceTemp 5%positive)
  (constant_affine_body_model 3%positive 50%positive 5 ncn_leaf)
  (AffineSourceAxis 3%positive 50%positive(MemorySourceConstant 5) ncn_leaf(AffineSourceLeaf ncn_leaf)).
Definition ncn_source := nested_constant_model_source 1%positive 4%positive 2%positive 5%positive
  51%positive 3%positive 50%positive 5 ncn_leaf.
Definition ncn_parameters := [4%positive;5%positive;7%positive].
Definition ncn_live := [1%positive;2%positive;3%positive;7%positive;10%positive;11%positive;50%positive;51%positive].
Definition ncn_proposal result := AffineGuardProposal 1%positive 4%positive ncn_body ncn_child
  [(0,16);(0,16);(0,5);(0,16);(0,16);(-32,33)] 0 1280 [10%positive] [ncn_operation]
  [(0,16);(0,16);(-32,33)] 0 16 [(0,16);(0,5)]
  [101%positive;104%positive;102%positive;105%positive;103%positive;106%positive] result.
Definition ncn_checked result := match check_affine_guard_package ncn_source ncn_parameters ncn_live
  (ncn_proposal result) with Some _=>true|None=>false end.
Example nested_constant_body_parameter_package_checked : ncn_checked 107%positive=true.
Proof. vm_compute; reflexivity. Qed.
Example nested_constant_public_result_refused : ncn_checked 7%positive=false.
Proof. vm_compute; reflexivity. Qed.
Definition ncn_package : affine_guard_package ncn_source ncn_parameters ncn_live(ncn_proposal 107%positive).
Proof.
  pose proof nested_constant_body_parameter_package_checked as CHECK; unfold ncn_checked in CHECK.
  destruct(check_affine_guard_package ncn_source ncn_parameters ncn_live(ncn_proposal 107%positive));
    [assumption|discriminate].
Defined.
Example nested_constant_checked_nest_shape : affine_proposal_nest(ncn_proposal 107%positive)=
  nested_constant_model_nest 1%positive 4%positive 2%positive 5%positive 51%positive 3%positive 50%positive
    5 ncn_leaf(AffineSourceLeaf ncn_leaf).
Proof. reflexivity. Qed.

Definition ncn_temps root child body_parameter := PTree.set 1%positive(Vint Int.zero)
  (PTree.set 4%positive(Vint(Int.repr root))(PTree.set 5%positive(Vint(Int.repr child))
    (PTree.set 7%positive(Vint(Int.repr body_parameter))(PTree.empty val)))).
Example nested_constant_numeric_accepts ge locals memory :
  nested_constant_numeric_flag 4%positive 5%positive ncn_parameters(ncn_proposal 107%positive)
    (Entry ge locals(ncn_temps 2 3 4) memory)=true.
Proof. vm_compute; reflexivity. Qed.
Example nested_constant_numeric_outside_profile_refused ge locals memory :
  nested_constant_numeric_flag 4%positive 5%positive ncn_parameters(ncn_proposal 107%positive)
    (Entry ge locals(ncn_temps 16 3 4) memory)=false.
Proof. vm_compute; reflexivity. Qed.

(** The undefined BODY-only parameter, pointer, and source counters are
    absent from these environments. Neither refusal runs the numeric probe. *)
Definition ncn_empty_root_temps := PTree.set 4%positive(Vint Int.zero)(PTree.empty val).
Definition ncn_empty_child_temps := PTree.set 4%positive(Vint(Int.repr 2))
  (PTree.set 5%positive(Vint Int.zero)(PTree.empty val)).
Theorem nested_constant_empty_root_actual_refusal fe ge locals memory :
  exec_stmt fe ge locals ncn_empty_root_temps memory
    (nested_constant_numeric_code 4%positive 5%positive 107%positive(affine_package_guard_code ncn_package))
    E0(PTree.set 107%positive(Vint Int.zero)ncn_empty_root_temps) memory Out_normal.
Proof.
  apply nested_constant_numeric_root_refusal; [exists Int.zero|]; vm_compute; reflexivity.
Qed.
Theorem nested_constant_empty_child_actual_refusal fe ge locals memory :
  exec_stmt fe ge locals ncn_empty_child_temps memory
    (nested_constant_numeric_code 4%positive 5%positive 107%positive(affine_package_guard_code ncn_package))
    E0(PTree.set 107%positive(Vint Int.zero)ncn_empty_child_temps) memory Out_normal.
Proof.
  apply nested_constant_numeric_child_refusal; [exists(Int.repr 2)|exists Int.zero| |]; vm_compute; reflexivity.
Qed.

Print Assumptions nested_constant_body_parameter_package_checked.
Print Assumptions nested_constant_public_result_refused.
Print Assumptions nested_constant_checked_nest_shape.
Print Assumptions nested_constant_numeric_accepts.
Print Assumptions nested_constant_numeric_outside_profile_refused.
Print Assumptions nested_constant_empty_root_actual_refusal.
Print Assumptions nested_constant_empty_child_actual_refusal.
