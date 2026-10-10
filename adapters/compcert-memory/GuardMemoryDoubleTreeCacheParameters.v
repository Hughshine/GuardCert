From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceTreeState GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCaptureReceipt
  GuardMemoryDoubleTreeCaptureFacts GuardMemoryDoubleTreeCacheFrame GuardMemoryDoubleTreeActiveValuation
  GuardMemoryLongExpressionCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tree_cached_value (cache : ident -> ident) (temps : temp_env) header :=
  match temps ! (cache header) with Some (Vint word)=>Int.signed word | _=>0 end.
Definition double_tree_cached_parameters tree cache temps :=
  map (double_tree_cached_value cache temps) (double_source_tree_parameters tree).

Theorem double_tree_accepted_cache_words ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  forall headers, incl (double_source_tree_headers tree) headers -> double_tree_cache_distinct headers cache ->
  (forall header, In header headers -> cache header<>flag) -> accepted=true ->
  forall header, In header (double_source_tree_active_headers (double_tree_observed_value ge memory) tree) ->
    double_tree_cache_word ge memory cache after header /\
    Int.min_signed<=double_tree_observed_value ge memory header<=Int.max_signed.
Proof.
  intro RECEIPT; induction RECEIPT; intros headers HEADERS DISTINCT FRESH ACCEPT header MEMBER; try discriminate;
    try solve [contradiction].
  - pose proof (@double_tree_flag_values_unique middle flag accepted_first true
      (double_tree_capture_receipt_flag RECEIPT1) (double_tree_capture_receipt_started RECEIPT2 ACCEPT)) as FIRST.
    apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + destruct (@IHRECEIPT1 headers
        ltac:(intros key INSIDE; apply HEADERS; cbn; apply in_or_app; left; exact INSIDE)
        DISTINCT FRESH FIRST header MEMBER) as [WORD RANGE].
      split; [|exact RANGE].
      apply (@double_tree_capture_preserves_cache ge locals memory cache flag lower upper second middle after accepted
        RECEIPT2 headers header); try assumption.
      * intros key INSIDE; apply HEADERS; cbn; apply in_or_app; right; exact INSIDE.
      * apply HEADERS; cbn; apply in_or_app; left; eapply double_source_tree_active_headers_subset; exact MEMBER.
      * apply FRESH,HEADERS; cbn; apply in_or_app; left; eapply double_source_tree_active_headers_subset; exact MEMBER.
    + apply (@IHRECEIPT2 headers); try assumption.
      intros key INSIDE; apply HEADERS; cbn; apply in_or_app; right; exact INSIDE.
  - pose proof (@double_tree_accepted_active_value ge locals memory start bound block input
      (lower (tree_bound_header bound)) (upper (tree_bound_header bound)) H0 H1 (proj1 H2) (proj2 H3) H4) as ACTIVE.
    rewrite H5 in ACTIVE; cbn [double_source_tree_active_headers] in MEMBER; rewrite <- ACTIVE in MEMBER.
    destruct MEMBER as [SAME|[]]; subst header; split.
    + unfold double_tree_cache_word; rewrite (@double_tree_captured_cache temps bound cache flag input lower upper
        ltac:(intro SAME; apply (FRESH _ (HEADERS _ (or_introl eq_refl))); congruence) H4).
      rewrite memory_long_loword_signed,(@double_tree_observed_load ge locals memory _ block input H0 H1); reflexivity.
    + rewrite (@double_tree_observed_load ge locals memory _ block input H0 H1).
      apply memory_long_expression_accept_spec in H4; lia.
  - pose proof (@double_tree_accepted_active_value ge locals memory start bound block input
      (lower (tree_bound_header bound)) (upper (tree_bound_header bound)) H0 H1 (proj1 H2) (proj2 H3) H4) as ACTIVE.
    rewrite H5 in ACTIVE; cbn [double_source_tree_active_headers] in MEMBER; rewrite <- ACTIVE in MEMBER.
    destruct MEMBER as [SAME|MEMBER].
    + subst header; split.
      * apply (@double_tree_capture_preserves_cache ge locals memory cache flag lower upper child _ after accepted
          RECEIPT headers (tree_bound_header bound)); try assumption.
        -- intros key INSIDE; apply HEADERS; cbn; right; exact INSIDE.
        -- apply HEADERS; cbn; left; reflexivity.
        -- apply FRESH,HEADERS; cbn; left; reflexivity.
        -- unfold double_tree_cache_word; rewrite (@double_tree_captured_cache temps bound cache flag input lower upper
             ltac:(intro SAME; apply (FRESH _ (HEADERS _ (or_introl eq_refl))); congruence) H4).
           rewrite memory_long_loword_signed,(@double_tree_observed_load ge locals memory _ block input H0 H1); reflexivity.
      * rewrite (@double_tree_observed_load ge locals memory _ block input H0 H1).
        apply memory_long_expression_accept_spec in H4; lia.
    + apply (@IHRECEIPT headers); try assumption.
      intros key INSIDE; apply HEADERS; cbn; right; exact INSIDE.
Qed.

Theorem double_tree_accepted_cached_values ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  double_tree_cache_distinct (double_source_tree_headers tree) cache ->
  (forall header, In header (double_source_tree_headers tree) -> cache header<>flag) -> accepted=true ->
  double_tree_active_values_agree tree (double_tree_observed_value ge memory) (double_tree_cached_value cache after).
Proof.
  intros RECEIPT DISTINCT FRESH ACCEPT header MEMBER.
  destruct (@double_tree_accepted_cache_words ge locals memory cache flag lower upper tree temps after accepted RECEIPT
    (double_source_tree_headers tree) (incl_refl _) DISTINCT FRESH ACCEPT header MEMBER) as [WORD RANGE].
  unfold double_tree_cached_value; rewrite WORD,Int.signed_repr by exact RANGE; reflexivity.
Qed.
Theorem double_tree_accepted_cached_headers ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  double_tree_cache_distinct (double_source_tree_headers tree) cache ->
  (forall header, In header (double_source_tree_headers tree) -> cache header<>flag) -> accepted=true ->
  double_source_tree_header_words ge locals
    (double_source_tree_active_headers (double_tree_cached_value cache after) tree)
    (double_tree_cached_value cache after) memory /\ double_tree_capture_range_facts tree (double_tree_cached_value cache after).
Proof.
  intros RECEIPT DISTINCT FRESH ACCEPT.
  pose proof (@double_tree_accepted_cached_values ge locals memory cache flag lower upper tree temps after accepted
    RECEIPT DISTINCT FRESH ACCEPT) as AGREE.
  destruct (double_tree_capture_accepted_headers RECEIPT ACCEPT) as [WORDS RANGES]; split.
  - eapply double_tree_active_words_agree; eassumption.
  - eapply double_tree_active_ranges_agree; eassumption.
Qed.

Print Assumptions double_tree_accepted_cache_words.
Print Assumptions double_tree_accepted_cached_values.
Print Assumptions double_tree_accepted_cached_headers.
