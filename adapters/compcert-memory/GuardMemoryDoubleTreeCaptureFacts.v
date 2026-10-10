From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceTreeState GuardMemoryDoubleTreeCaptureLicense GuardMemoryDoubleTreeCaptureData
  GuardMemoryDoubleTreeCaptureControl GuardMemoryDoubleTreeCaptureReceipt GuardMemoryLongExpressionCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A proof valuation is total even when an unreachable header has no defined
    load. Generated code never evaluates this mathematical function. Only the
    active-header theorem below supplies usable load receipts. *)
Definition double_tree_observed_value (ge : genv) memory header : Z :=
  match Genv.find_symbol ge header with
  | Some block=>match Mem.load Mint64 memory block 0 with Some (Vlong word)=>Int64.signed word | _=>0 end
  | None=>0 end.
Lemma double_tree_observed_load ge locals memory header block input :
  double_global_binding ge locals header block -> Mem.load Mint64 memory block 0=Some (Vlong input) ->
  double_tree_observed_value ge memory header=Int64.signed input.
Proof. intros BIND LOAD; unfold double_tree_observed_value; rewrite (proj2 BIND),LOAD; reflexivity. Qed.
Fixpoint double_tree_capture_range_facts tree valuation : Prop := match tree with
  | DoubleTreeSkip | DoubleTreePoint _ _=>True
  | DoubleTreeSequence first second=>double_tree_capture_range_facts first valuation /\ double_tree_capture_range_facts second valuation
  | DoubleTreeRange _ _ start bound child=>
      Int64.min_signed<=double_tree_bound_value valuation bound<=Int64.max_signed /\
      (if Int.signed start <? double_tree_bound_value valuation bound then double_tree_capture_range_facts child valuation else True)
  end.
Lemma double_tree_flag_values_unique temps flag first second :
  double_tree_flag_value temps flag first -> double_tree_flag_value temps flag second -> first=second.
Proof.
  unfold double_tree_flag_value; intros FIRST SECOND; destruct first,second; try reflexivity;
    rewrite FIRST in SECOND; discriminate.
Qed.
Lemma double_tree_capture_receipt_started ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  accepted=true -> double_tree_flag_value temps flag true.
Proof.
  intro RECEIPT; induction RECEIPT; intro ACCEPT; try discriminate; try assumption.
  pose proof (IHRECEIPT2 ACCEPT) as MIDDLE.
  pose proof (@double_tree_flag_values_unique middle flag accepted_first true
    (double_tree_capture_receipt_flag RECEIPT1) MIDDLE) as FIRST.
  apply IHRECEIPT1; exact FIRST.
Qed.
Lemma double_tree_accepted_active_value ge locals memory start bound block input lower upper :
  double_global_binding ge locals (tree_bound_header bound) block -> Mem.load Mint64 memory block 0=Some (Vlong input) ->
  Int.min_signed<=lower -> upper<=Int.max_signed -> memory_long_expression_accept input lower upper=true ->
  double_tree_word_active start bound input=
    (Int.signed start <? double_tree_bound_value (double_tree_observed_value ge memory) bound).
Proof.
  intros BIND LOAD LOW HIGH ACCEPT; unfold double_tree_word_active,double_tree_bound_value.
  rewrite Int64.signed_repr by (apply memory_i32_range_is_i64,Int.signed_range).
  rewrite (@double_tree_observed_load ge locals memory _ block input BIND LOAD).
  rewrite (@double_tree_accepted_word_bound bound input lower upper LOW HIGH ACCEPT); reflexivity.
Qed.
Theorem double_tree_capture_accepted_headers ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted -> accepted=true ->
  double_source_tree_header_words ge locals
    (double_source_tree_active_headers (double_tree_observed_value ge memory) tree)
    (double_tree_observed_value ge memory) memory /\
  double_tree_capture_range_facts tree (double_tree_observed_value ge memory).
Proof.
  intro RECEIPT; induction RECEIPT; intro ACCEPT; try discriminate.
  - split; [intros header MEMBER; contradiction|exact I].
  - split; [intros header MEMBER; contradiction|exact I].
  - pose proof (@double_tree_flag_values_unique middle flag accepted_first true
      (double_tree_capture_receipt_flag RECEIPT1) (double_tree_capture_receipt_started RECEIPT2 ACCEPT)) as FIRST.
    destruct (IHRECEIPT1 FIRST) as [WORDS1 RANGE1]; destruct (IHRECEIPT2 ACCEPT) as [WORDS2 RANGE2].
    split; [|split; assumption].
    intros header MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER]; [apply WORDS1|apply WORDS2]; exact MEMBER.
  - pose proof (@double_tree_accepted_active_value ge locals memory start bound block input
      (lower (tree_bound_header bound)) (upper (tree_bound_header bound)) H0 H1 (proj1 H2) (proj2 H3) H4) as ACTIVE.
    rewrite H5 in ACTIVE; symmetry in ACTIVE.
    split.
    + cbn [double_source_tree_active_headers]; rewrite ACTIVE; intros header [SAME|[]]; subst header.
      exists block; split; [exact H0|].
      rewrite (@double_tree_observed_load ge locals memory _ block input H0 H1),Int64.repr_signed; exact H1.
    + cbn [double_tree_capture_range_facts]; rewrite ACTIVE; split; [|exact I].
      unfold double_tree_bound_value; rewrite (@double_tree_observed_load ge locals memory _ block input H0 H1).
      eapply double_tree_accepted_bound_range; [exact (proj1 H2)|exact (proj2 H3)|exact H4].
  - destruct (IHRECEIPT ACCEPT) as [WORDS RANGE].
    pose proof (@double_tree_accepted_active_value ge locals memory start bound block input
      (lower (tree_bound_header bound)) (upper (tree_bound_header bound)) H0 H1 (proj1 H2) (proj2 H3) H4) as ACTIVE.
    rewrite H5 in ACTIVE; symmetry in ACTIVE.
    split.
    + cbn [double_source_tree_active_headers]; rewrite ACTIVE; intros header [SAME|MEMBER].
      * subst header; exists block; split; [exact H0|].
        rewrite (@double_tree_observed_load ge locals memory _ block input H0 H1),Int64.repr_signed; exact H1.
      * apply WORDS; exact MEMBER.
    + cbn [double_tree_capture_range_facts]; rewrite ACTIVE; split; [|exact RANGE].
      unfold double_tree_bound_value; rewrite (@double_tree_observed_load ge locals memory _ block input H0 H1).
      eapply double_tree_accepted_bound_range; [exact (proj1 H2)|exact (proj2 H3)|exact H4].
Qed.

Print Assumptions double_tree_observed_load.
Print Assumptions double_tree_flag_values_unique.
Print Assumptions double_tree_capture_receipt_started.
Print Assumptions double_tree_accepted_active_value.
Print Assumptions double_tree_capture_accepted_headers.
