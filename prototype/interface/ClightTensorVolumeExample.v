From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightCondition ClightCountedLoop ClightPureExpr.
From GuardMemory Require Import GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorAccess.
From GuardInterface Require Import ClightTensorVolumeGuard ClightReadonlyRewrite.
Import ListNotations.
Local Open Scope Z_scope.

Definition tensor_example_codes := map(fun identifier=>Etempvar identifier type_int32s)
  [1%positive;2%positive;3%positive].
Definition tensor_example_temps x y z := PTree.set 1%positive(Vint(Int.repr x))
  (PTree.set 2%positive(Vint(Int.repr y))(PTree.set 3%positive(Vint(Int.repr z))(PTree.empty val))).
Lemma tensor_example_words ge locals memory x y z :
  signed_range x -> signed_range y -> signed_range z ->
  Forall2(tensor_guard_operand(Entry ge locals(tensor_example_temps x y z)memory))tensor_example_codes[x;y;z].
Proof.
  intros X Y Z; unfold tensor_example_codes; cbn [map]; repeat apply Forall2_cons; [| | |constructor].
  all: unfold tensor_guard_operand,tensor_operand; cbn [entry_ge entry_env entry_temps entry_memory].
  all: split; [split; [reflexivity|split; [constructor|constructor; reflexivity]]|assumption].
Qed.
Lemma tensor_example_guard ge locals memory x y z :
  signed_range x -> signed_range y -> signed_range z ->
  decision_run(Entry ge locals(tensor_example_temps x y z)memory)(tensor_volume_guard tensor_example_codes)
    (tensor_volume_check tensor_volume_cap 1[x;y;z]).
Proof.
  intros X Y Z; apply tensor_volume_guard_run.
  - apply tensor_example_words; assumption.
  - unfold tensor_operand; split; [reflexivity|split; [constructor|constructor]].
  - pose proof tensor_volume_cap_range; lia.
Qed.
Theorem tensor_example_runtime_stride_17 ge locals memory :
  decision_run(Entry ge locals(tensor_example_temps 3 17 5)memory)(tensor_volume_guard tensor_example_codes)true.
Proof. apply tensor_example_guard; unfold signed_range; change Int.min_signed with(-2147483648); change Int.max_signed with 2147483647; lia. Qed.
Theorem tensor_example_runtime_stride_31 ge locals memory :
  decision_run(Entry ge locals(tensor_example_temps 3 31 5)memory)(tensor_volume_guard tensor_example_codes)true.
Proof. apply tensor_example_guard; unfold signed_range; change Int.min_signed with(-2147483648); change Int.max_signed with 2147483647; lia. Qed.
Theorem tensor_example_signed_max_accepted ge locals memory :
  decision_run(Entry ge locals(tensor_example_temps Int.max_signed 1 1)memory)(tensor_volume_guard tensor_example_codes)true.
Proof. apply tensor_example_guard; unfold signed_range; change Int.min_signed with(-2147483648); change Int.max_signed with 2147483647; lia. Qed.
Theorem tensor_example_overflow_refused ge locals memory :
  decision_run(Entry ge locals(tensor_example_temps 46341 46341 1)memory)(tensor_volume_guard tensor_example_codes)false.
Proof. apply tensor_example_guard; unfold signed_range; change Int.min_signed with(-2147483648); change Int.max_signed with 2147483647; lia. Qed.
Theorem tensor_example_signed_max_product_refused ge locals memory :
  decision_run(Entry ge locals(tensor_example_temps Int.max_signed 2 1)memory)(tensor_volume_guard tensor_example_codes)false.
Proof. apply tensor_example_guard; unfold signed_range; change Int.min_signed with(-2147483648); change Int.max_signed with 2147483647; lia. Qed.
Theorem tensor_example_uninitialized_suffix_safe ge locals memory :
  readonly_tree_safe(Entry ge locals(PTree.set 1%positive(Vint Int.zero)(PTree.empty val))memory)
    (tensor_volume_guard tensor_example_codes).
Proof.
  apply tensor_volume_guard_refuses_first_safe with(dimension:=0).
  - unfold tensor_guard_operand,tensor_operand; split; [split; [reflexivity|split; [constructor|constructor; reflexivity]]|].
    unfold signed_range; change Int.min_signed with(-2147483648); change Int.max_signed with 2147483647; lia.
  - lia.
  - repeat constructor.
Qed.
Example tensor_example_different_strides :
  tensor_index[3;17;5][2;4;3]=Some 193 /\ tensor_index[3;31;5][2;4;3]=Some 333.
Proof. vm_compute; auto. Qed.
Example tensor_example_outside_axis_refused : tensor_index[3;17;5][2;17;0]=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_example_missing_axis_refused : tensor_index[3;17;5][2;4]=None.
Proof. vm_compute; reflexivity. Qed.
Example tensor_example_zero_dimension_refused : tensor_layout_flag[3;0;5]=false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions tensor_example_runtime_stride_17.
Print Assumptions tensor_example_runtime_stride_31.
Print Assumptions tensor_example_signed_max_accepted.
Print Assumptions tensor_example_overflow_refused.
Print Assumptions tensor_example_signed_max_product_refused.
Print Assumptions tensor_example_uninitialized_suffix_safe.
Print Assumptions tensor_example_different_strides.
Print Assumptions tensor_example_outside_axis_refused.
Print Assumptions tensor_example_missing_axis_refused.
Print Assumptions tensor_example_zero_dimension_refused.
