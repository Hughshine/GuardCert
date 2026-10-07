From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From GuardInterface Require Import ClightAffineJointObservation ClightConstantJointInnerScan ClightConstantJointOuterScan.
Import ListNotations.
Set Implicit Arguments.

(** Blocks, offsets and loaded words are proof receipts obtained at runtime
    entry. Generated check syntax depends only on the observer expressions. *)
Lemma joint_comparison_code_same_tests values flag first second :
  map(affine_joint_comparison_test values) first=map(affine_joint_comparison_test values) second ->
  affine_joint_comparison_code values flag first=affine_joint_comparison_code values flag second.
Proof.
  revert second; induction first as [|comparison rest IH]; intros [|other tail] SAME;
    cbn in SAME; try discriminate; [reflexivity|].
  assert(TEST:affine_joint_comparison_test values comparison=affine_joint_comparison_test values other)
    by exact(f_equal(fun tests=>hd(affine_joint_comparison_test values comparison) tests) SAME).
  assert(REST:map(affine_joint_comparison_test values) rest=map(affine_joint_comparison_test values) tail)
    by exact(f_equal(@tl expr) SAME).
  change (Ssequence(GuardMemory.GuardMemoryBooleanScan.memory_boolean_test_body flag(affine_joint_comparison_test values comparison))
    (affine_joint_comparison_code values flag rest)=
    Ssequence(GuardMemory.GuardMemoryBooleanScan.memory_boolean_test_body flag(affine_joint_comparison_test values other))
    (affine_joint_comparison_code values flag tail)).
  rewrite TEST,(IH tail REST); reflexivity.
Qed.

Lemma joint_comparison_tests_same_addresses values operations first second :
  map word_observer_address first=map word_observer_address second ->
  map(affine_joint_comparison_test values)(affine_joint_comparisons first operations)=
    map(affine_joint_comparison_test values)(affine_joint_comparisons second operations).
Proof.
  revert second; induction first as [|observer rest IH]; intros [|other tail] SAME;
    cbn in SAME; try discriminate; [reflexivity|].
  injection SAME as ADDRESS REST.
  unfold affine_joint_comparisons; cbn [flat_map]; rewrite !map_app; f_equal.
  - rewrite !map_map; apply map_ext; intro operation.
    unfold affine_joint_comparison_test; cbn [fst snd]; rewrite ADDRESS; reflexivity.
  - apply IH; exact REST.
Qed.

Theorem joint_observation_leaf_same_addresses first second operations values flag :
  map word_observer_address first=map word_observer_address second ->
  affine_joint_observation_leaf first operations values flag=affine_joint_observation_leaf second operations values flag.
Proof.
  intro ADDRESSES; unfold affine_joint_observation_leaf.
  apply joint_comparison_code_same_tests,joint_comparison_tests_same_addresses; exact ADDRESSES.
Qed.

Theorem constant_joint_outer_same_addresses root_cache child_cache row_cursor row_limit column_cursor column_limit
  flag nest controls values first second operations :
  map word_observer_address first=map word_observer_address second ->
  constant_joint_outer_statement root_cache child_cache row_cursor row_limit column_cursor column_limit
    flag nest controls values first operations=
  constant_joint_outer_statement root_cache child_cache row_cursor row_limit column_cursor column_limit
    flag nest controls values second operations.
Proof.
  intro ADDRESSES; unfold constant_joint_outer_statement,constant_joint_inner_statement,constant_joint_inner_body.
  rewrite(@joint_observation_leaf_same_addresses first second operations values flag ADDRESSES); reflexivity.
Qed.

Print Assumptions joint_comparison_code_same_tests.
Print Assumptions joint_comparison_tests_same_addresses.
Print Assumptions joint_observation_leaf_same_addresses.
Print Assumptions constant_joint_outer_same_addresses.
