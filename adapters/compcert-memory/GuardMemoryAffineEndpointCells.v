From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryFiniteAliasCondition GuardMemoryFiniteFootprint GuardMemoryFootprintCapabilities GuardMemoryBufferOffsets
  GuardMemoryNaryAffineExpressions GuardMemoryBooleanScan GuardMemoryAffinePairScan.
From GuardMemory Require Import GuardMemoryAffineEndpointMath.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_endpoint_pair_check locations count first second first_term second_term :=
  memory_boolean_scan_result (fun index =>
    memory_cell_pair_address_check locations
      (point_cell first (memory_nary_index_value first_term [0]))
      (point_cell second (memory_nary_index_value second_term [index])) &&
    memory_cell_pair_address_check locations
      (point_cell first (memory_nary_index_value first_term [index]))
      (point_cell second (memory_nary_index_value second_term [0]))) 0 (Z.to_nat count).

Lemma memory_nary_one_value term index :
  memory_nary_index_value term [index] = hd 0 (fst term)*index+snd term.
Proof. destruct term as [[|factor rest] bias]; unfold memory_nary_index_value; cbn; try rewrite dot_product_nil_right; ring. Qed.

Lemma memory_pointer_pair_physical_check temps extent memory first second i j first_block first_base second_block second_base :
  first <> second ->
  temps ! first = Some (Vptr first_block first_base) -> temps ! second = Some (Vptr second_block second_base) ->
  memory_cell_capable (memory_multi_pointer_locations temps extent) memory (point_cell first i) ->
  memory_cell_capable (memory_multi_pointer_locations temps extent) memory (point_cell second j) ->
  memory_cell_pair_address_check (memory_multi_pointer_locations temps extent) (point_cell first i) (point_cell second j) =
    negb (Pos.eqb first_block second_block &&
      Z.eqb (memory_pointer_buffer_offset first_base i) (memory_pointer_buffer_offset second_base j)).
Proof.
  intros DISTINCT FIRST SECOND [left [LEFT OTHER]] [right [RIGHT REST]].
  destruct (@memory_multi_pointer_location_inverse temps extent (point_cell first i) left LEFT)
    as [fb [fp [fi [FB [FI [FR FL]]]]]].
  destruct (@memory_multi_pointer_location_inverse temps extent (point_cell second j) right RIGHT)
    as [sb [sp [sj [SB [SJ [SR SL]]]]]].
  cbn [arr_id arr_index point_cell] in FB,FI,SB,SJ.
  assert (fb=first_block /\ fp=first_base) by (split; congruence).
  assert (sb=second_block /\ sp=second_base) by (split; congruence).
  destruct H as [-> ->]; destruct H0 as [-> ->]; inversion FI; inversion SJ; subst fi sj.
  subst left right; unfold memory_cell_pair_address_check.
  destruct memory_cell_identity_dec as [SAME|];
    [apply (f_equal arr_id) in SAME; cbn [arr_id point_cell] in SAME; contradiction|].
  rewrite LEFT,RIGHT; reflexivity.
Qed.

Theorem memory_affine_endpoint_pair_complete temps extent memory count first second first_term second_term :
  first <> second -> hd 0 (fst first_term) = hd 0 (fst second_term) -> 0 <= count ->
  (forall index, 0 <= index < count ->
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell first (memory_nary_index_value first_term [index])) /\
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell second (memory_nary_index_value second_term [index]))) ->
  memory_affine_endpoint_pair_check (memory_multi_pointer_locations temps extent) count first second first_term second_term = true ->
  memory_affine_range_pair_check (memory_multi_pointer_locations temps extent) count first second first_term second_term = true.
Proof.
  intros DISTINCT SLOPE COUNT CAPS CHECK.
  unfold memory_affine_range_pair_check; rewrite memory_boolean_scan_member,Z2Nat.id by exact COUNT.
  intros i I; rewrite memory_boolean_scan_member,Z2Nat.id by exact COUNT; intros j J.
  assert (IR : 0<=i<count) by lia; assert (JR : 0<=j<count) by lia.
  destruct (CAPS i IR) as [FIRST_CAP _]; destruct (CAPS j JR) as [_ SECOND_CAP].
  destruct FIRST_CAP as [left [LEFT MORE]]; destruct SECOND_CAP as [right [RIGHT REST]].
  destruct (@memory_multi_pointer_location_inverse temps extent _ left LEFT)
    as [fb [fp [fi [FB [FI [FR FL]]]]]].
  destruct (@memory_multi_pointer_location_inverse temps extent _ right RIGHT)
    as [sb [sp [sj [SB [SJ [SR SL]]]]]].
  cbn [arr_id arr_index point_cell] in FB,FI,SB,SJ.
  rewrite (@memory_pointer_pair_physical_check temps extent memory first second
    (memory_nary_index_value first_term [i]) (memory_nary_index_value second_term [j]) fb fp sb sp
    DISTINCT FB SB (proj1 (CAPS i IR)) (proj2 (CAPS j JR))).
  apply negb_true_iff; destruct (Pos.eqb fb sb) eqn:BLOCK; [|reflexivity].
  apply Pos.eqb_eq in BLOCK; subst sb; cbn [andb].
  apply Z.eqb_neq; intro SAME.
  unfold memory_pointer_buffer_offset,memory_buffer_offset in SAME.
  rewrite !memory_nary_one_value,SLOPE in SAME.
  change (memory_affine_endpoint_offset Ptrofs.modulus (Ptrofs.unsigned fp) (hd 0 (fst second_term)) (snd first_term) i =
    memory_affine_endpoint_offset Ptrofs.modulus (Ptrofs.unsigned sp) (hd 0 (fst second_term)) (snd second_term) j) in SAME.
  destruct (@memory_affine_endpoint_overlap Ptrofs.modulus (Ptrofs.unsigned fp) (Ptrofs.unsigned sp)
    (hd 0 (fst second_term)) (snd first_term) (snd second_term) count i j ltac:(pose proof Ptrofs.modulus_pos; lia) IR JR SAME)
    as [index [INDEX [BAD|BAD]]].
  all: unfold memory_affine_endpoint_pair_check in CHECK; rewrite memory_boolean_scan_member in CHECK;
    specialize (CHECK index ltac:(rewrite Z2Nat.id by exact COUNT; lia));
    apply andb_true_iff in CHECK as [HEAD_FIRST HEAD_SECOND];
    assert (ZERO : 0<=0<count) by lia.
  - rewrite (@memory_pointer_pair_physical_check temps extent memory first second
      (memory_nary_index_value first_term [0]) (memory_nary_index_value second_term [index]) fb fp fb sp
      DISTINCT FB SB (proj1 (CAPS 0 ZERO)) (proj2 (CAPS index INDEX))) in HEAD_FIRST.
    rewrite Pos.eqb_refl in HEAD_FIRST; cbn [andb] in HEAD_FIRST.
    unfold memory_pointer_buffer_offset,memory_buffer_offset in HEAD_FIRST.
    rewrite !memory_nary_one_value,SLOPE in HEAD_FIRST.
    change (negb (Z.eqb (memory_affine_endpoint_offset Ptrofs.modulus (Ptrofs.unsigned fp) (hd 0 (fst second_term)) (snd first_term) 0)
      (memory_affine_endpoint_offset Ptrofs.modulus (Ptrofs.unsigned sp) (hd 0 (fst second_term)) (snd second_term) index)) = true) in HEAD_FIRST.
    rewrite BAD,Z.eqb_refl in HEAD_FIRST; discriminate.
  - rewrite (@memory_pointer_pair_physical_check temps extent memory first second
      (memory_nary_index_value first_term [index]) (memory_nary_index_value second_term [0]) fb fp fb sp
      DISTINCT FB SB (proj1 (CAPS index INDEX)) (proj2 (CAPS 0 ZERO))) in HEAD_SECOND.
    rewrite Pos.eqb_refl in HEAD_SECOND; cbn [andb] in HEAD_SECOND.
    unfold memory_pointer_buffer_offset,memory_buffer_offset in HEAD_SECOND.
    rewrite !memory_nary_one_value,SLOPE in HEAD_SECOND.
    change (negb (Z.eqb (memory_affine_endpoint_offset Ptrofs.modulus (Ptrofs.unsigned fp) (hd 0 (fst second_term)) (snd first_term) index)
      (memory_affine_endpoint_offset Ptrofs.modulus (Ptrofs.unsigned sp) (hd 0 (fst second_term)) (snd second_term) 0)) = true) in HEAD_SECOND.
    rewrite BAD,Z.eqb_refl in HEAD_SECOND; discriminate.
Qed.
Lemma memory_nary_one_constant term : hd 0 (fst term) = 0 ->
  forall first second, memory_nary_index_value term [first] = memory_nary_index_value term [second].
Proof. intros ZERO first second; rewrite !memory_nary_one_value,ZERO; ring. Qed.

Theorem memory_affine_endpoint_pair_first_constant locations count first second first_term second_term :
  hd 0 (fst first_term) = 0 -> 0 <= count ->
  memory_affine_endpoint_pair_check locations count first second first_term second_term = true ->
  memory_affine_range_pair_check locations count first second first_term second_term = true.
Proof.
  intros ZERO COUNT CHECK.
  unfold memory_affine_range_pair_check; rewrite memory_boolean_scan_member,Z2Nat.id by exact COUNT.
  intros i I; rewrite memory_boolean_scan_member,Z2Nat.id by exact COUNT; intros j J.
  unfold memory_affine_endpoint_pair_check in CHECK; rewrite memory_boolean_scan_member in CHECK.
  specialize (CHECK j ltac:(rewrite Z2Nat.id by exact COUNT; lia)); apply andb_true_iff in CHECK as [FIRST SECOND].
  rewrite (@memory_nary_one_constant first_term ZERO i 0); exact FIRST.
Qed.
Theorem memory_affine_endpoint_pair_second_constant locations count first second first_term second_term :
  hd 0 (fst second_term) = 0 -> 0 <= count ->
  memory_affine_endpoint_pair_check locations count first second first_term second_term = true ->
  memory_affine_range_pair_check locations count first second first_term second_term = true.
Proof.
  intros ZERO COUNT CHECK.
  unfold memory_affine_range_pair_check; rewrite memory_boolean_scan_member,Z2Nat.id by exact COUNT.
  intros i I; rewrite memory_boolean_scan_member,Z2Nat.id by exact COUNT; intros j J.
  unfold memory_affine_endpoint_pair_check in CHECK; rewrite memory_boolean_scan_member in CHECK.
  specialize (CHECK i ltac:(rewrite Z2Nat.id by exact COUNT; lia)); apply andb_true_iff in CHECK as [FIRST SECOND].
  rewrite (@memory_nary_one_constant second_term ZERO j 0); exact SECOND.
Qed.

Definition memory_affine_pair_fast (first_term second_term : constraint) :=
  (hd 0 (fst first_term) =? hd 0 (fst second_term)) ||
  (hd 0 (fst first_term) =? 0) || (hd 0 (fst second_term) =? 0).

Theorem memory_affine_pair_fast_complete temps extent memory count first second first_term second_term :
  first <> second -> 0 <= count ->
  (forall index, 0 <= index < count ->
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell first (memory_nary_index_value first_term [index])) /\
    memory_cell_capable (memory_multi_pointer_locations temps extent) memory
      (point_cell second (memory_nary_index_value second_term [index]))) ->
  memory_affine_pair_fast first_term second_term = true ->
  memory_affine_endpoint_pair_check (memory_multi_pointer_locations temps extent) count first second first_term second_term = true ->
  memory_affine_range_pair_check (memory_multi_pointer_locations temps extent) count first second first_term second_term = true.
Proof.
  intros DISTINCT COUNT CAPS FAST CHECK; unfold memory_affine_pair_fast in FAST.
  rewrite !orb_true_iff in FAST.
  destruct FAST as [[SAME|ZERO]|ZERO]; apply Z.eqb_eq in SAME || apply Z.eqb_eq in ZERO.
  - eapply memory_affine_endpoint_pair_complete; eassumption.
  - eapply memory_affine_endpoint_pair_first_constant; eassumption.
  - eapply memory_affine_endpoint_pair_second_constant; eassumption.
Qed.
Print Assumptions memory_affine_endpoint_pair_complete.
Print Assumptions memory_affine_pair_fast_complete.
