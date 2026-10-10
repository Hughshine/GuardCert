From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleTreeCaptureLicense GuardMemoryDoubleTreeCaptureData GuardMemoryLongControl
  GuardMemoryLongExpressionCapture GuardMemoryLongSourceAffine.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tree_word_active start bound input :=
  Int64.signed (Int64.repr (Int.signed start)) <? Int64.signed (double_tree_bound_word bound input).
Lemma double_tree_accepted_bound_range bound input lower upper :
  Int.min_signed<=lower -> upper<=Int.max_signed -> memory_long_expression_accept input lower upper=true ->
  Int64.min_signed<=Int64.signed input-
    match tree_bound_offset bound with None=>0 | Some offset=>Int.signed offset end<=Int64.max_signed.
Proof.
  intros LOW HIGH ACCEPT; apply memory_long_expression_accept_spec in ACCEPT.
  destruct (tree_bound_offset bound) as [offset|]; [pose proof (Int.signed_range offset)|];
    change (-2147483648<=lower) in LOW; change (upper<=2147483647) in HIGH;
    try change (-2147483648<=Int.signed offset<=2147483647) in H;
    change Int64.min_signed with (-9223372036854775808);
    change Int64.max_signed with 9223372036854775807; lia.
Qed.
Lemma double_tree_accepted_word_bound bound input lower upper :
  Int.min_signed<=lower -> upper<=Int.max_signed -> memory_long_expression_accept input lower upper=true ->
  Int64.signed (double_tree_bound_word bound input)=Int64.signed input-
    match tree_bound_offset bound with None=>0 | Some offset=>Int.signed offset end.
Proof.
  intros LOW HIGH ACCEPT; pose proof (@double_tree_accepted_bound_range bound input lower upper LOW HIGH ACCEPT) as RANGE.
  destruct bound as [header [offset|]]; cbn [double_tree_bound_word tree_bound_offset] in *; [|lia].
  rewrite <- (Int64.repr_signed input) at 1; rewrite long_source_repr_sub,Int64.signed_repr by exact RANGE; reflexivity.
Qed.
Lemma double_tree_cached_bound_execution ge locals temps memory bound cache input lower upper :
  Int.min_signed<=lower -> upper<=Int.max_signed -> memory_long_expression_accept input lower upper=true ->
  temps ! (cache (tree_bound_header bound))=Some (Vint (Int64.loword input)) ->
  eval_expr ge locals temps memory (double_tree_cached_bound bound cache) (Vlong (double_tree_bound_word bound input)).
Proof.
  intros LOW HIGH ACCEPT VALUE.
  pose proof (@memory_long_expression_accepted_i32 input lower upper LOW HIGH ACCEPT) as SIGNED.
  assert (CAST : eval_expr ge locals temps memory
    (Ecast (Etempvar (cache (tree_bound_header bound)) memory_signed_int_type) memory_long_type) (Vlong input)).
  { eapply eval_Ecast; [constructor; exact VALUE|].
    change (Some (Vlong (Int64.repr (Int.signed (Int64.loword input))))=Some (Vlong input)).
    rewrite SIGNED,Int64.repr_signed; reflexivity. }
  destruct bound as [header [offset|]]; cbn [double_tree_cached_bound double_tree_bound_word] in *; [|exact CAST].
  eapply eval_Ebinop; [exact CAST|constructor|reflexivity].
Qed.
Theorem double_tree_cached_active_execution ge locals temps memory start bound cache input lower upper :
  Int.min_signed<=lower -> upper<=Int.max_signed -> memory_long_expression_accept input lower upper=true ->
  temps ! (cache (tree_bound_header bound))=Some (Vint (Int64.loword input)) ->
  expression_test (double_tree_cached_active start bound cache) (Entry ge locals temps memory)
    (double_tree_word_active start bound input).
Proof.
  intros LOW HIGH ACCEPT VALUE; unfold double_tree_cached_active,double_tree_word_active.
  exists (Val.of_bool (Int.signed start <? Int64.signed (double_tree_bound_word bound input))); split.
  - eapply memory_long_test_execution; [reflexivity|destruct bound as [header [offset|]]; reflexivity|
      apply memory_i32_range_is_i64,Int.signed_range|apply Int64.signed_range| |].
    + unfold double_tree_initial; eapply eval_Ecast; [constructor|reflexivity].
    + rewrite Int64.repr_signed; eapply double_tree_cached_bound_execution; eassumption.
  - rewrite Int64.signed_repr by (apply memory_i32_range_is_i64,Int.signed_range).
    destruct (Int.signed start <? Int64.signed (double_tree_bound_word bound input)); reflexivity.
Qed.

Print Assumptions double_tree_accepted_bound_range.
Print Assumptions double_tree_accepted_word_bound.
Print Assumptions double_tree_cached_bound_execution.
Print Assumptions double_tree_cached_active_execution.
