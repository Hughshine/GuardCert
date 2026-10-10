From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCaptureReceipt GuardMemoryDoubleTreeCapturePrepared
  GuardMemoryDoubleTreeCacheFrame GuardMemoryDoubleTreeCacheParameters GuardMemoryLongExpressionCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Unreached headers have initialized zero slots. Candidate environments include
    that value even when a reached header's accepted profile excludes zero. *)
Definition double_tree_cache_interval (lower upper : ident -> Z) header value :=
  Z.min 0 (lower header)<=value<=Z.max 0 (upper header).
Definition double_tree_cache_environment headers cache lower upper (temps : temp_env) :=
  forall header, In header headers -> exists word, temps ! (cache header)=Some (Vint word) /\
    double_tree_cache_interval lower upper header (Int.signed word).
Lemma double_tree_initialization_preserves_zero headers cache : forall temps key,
  temps ! key=Some (Vint Int.zero) ->
  (double_tree_initialized_temps headers cache temps) ! key=Some (Vint Int.zero).
Proof.
  induction headers; intros temps key WORD; cbn [double_tree_initialized_temps]; [exact WORD|apply IHheaders].
  rewrite PTree.gsspec; destruct (peq key (cache a)); [reflexivity|exact WORD].
Qed.
Lemma double_tree_initialized_zero headers cache : forall temps header,
  In header headers -> (double_tree_initialized_temps headers cache temps) ! (cache header)=Some (Vint Int.zero).
Proof.
  induction headers; intros temps header MEMBER; [contradiction|].
  cbn [double_tree_initialized_temps]; destruct MEMBER as [SAME|MEMBER].
  - subst header; apply double_tree_initialization_preserves_zero,PTree.gss.
  - apply IHheaders; exact MEMBER.
Qed.
Theorem double_tree_initialized_environment headers cache lower upper temps :
  double_tree_cache_environment headers cache lower upper (double_tree_initialized_temps headers cache temps).
Proof.
  intros header MEMBER; exists Int.zero; split; [apply double_tree_initialized_zero; exact MEMBER|].
  unfold double_tree_cache_interval; change (Z.min 0 (lower header)<=0<=Z.max 0 (upper header)).
  split; [apply Z.le_min_l|apply Z.le_max_l].
Qed.
Lemma double_tree_captured_cache_interval temps bound cache flag input lower upper observer :
  cache observer<>flag -> (cache observer=cache (tree_bound_header bound) -> observer=tree_bound_header bound) ->
  Int.min_signed<=lower (tree_bound_header bound)<=Int.max_signed ->
  Int.min_signed<=upper (tree_bound_header bound)<=Int.max_signed ->
  (exists word, temps ! (cache observer)=Some (Vint word) /\ double_tree_cache_interval lower upper observer (Int.signed word)) ->
  exists word, (double_tree_captured temps bound cache flag input lower upper) ! (cache observer)=Some (Vint word) /\
    double_tree_cache_interval lower upper observer (Int.signed word).
Proof.
  intros FLAG DISTINCT LOW HIGH [word [WORD RANGE]].
  destruct (peq observer (tree_bound_header bound)) as [SAME|DIFFERENT].
  - subst observer; unfold double_tree_captured,memory_long_expression_captured; rewrite PTree.gso by exact FLAG.
    destruct (memory_long_expression_accept input (lower (tree_bound_header bound)) (upper (tree_bound_header bound))) eqn:ACCEPT.
    + exists (Int64.loword input); split; [apply PTree.gss|].
      rewrite (@memory_long_expression_accepted_i32 input _ _ (proj1 LOW) (proj2 HIGH) ACCEPT).
      apply memory_long_expression_accept_spec in ACCEPT; unfold double_tree_cache_interval.
      pose proof (Z.le_min_r 0 (lower (tree_bound_header bound))); pose proof (Z.le_max_r 0 (upper (tree_bound_header bound))); lia.
    + exists word; auto.
  - exists word; split; [|exact RANGE].
    unfold double_tree_captured; rewrite memory_long_expression_captured_frame; [exact WORD| |exact FLAG].
    intro SAME; apply DIFFERENT,DISTINCT; exact SAME.
Qed.
Theorem double_tree_capture_environment_preserved ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  forall headers, incl (double_source_tree_headers tree) headers -> double_tree_cache_distinct headers cache ->
  (forall header, In header headers -> cache header<>flag) ->
  double_tree_cache_environment headers cache lower upper temps -> double_tree_cache_environment headers cache lower upper after.
Proof.
  intro RECEIPT; induction RECEIPT; intros headers HEADERS DISTINCT FRESH ENV; try exact ENV.
  - apply IHRECEIPT2 with (headers:=headers); try assumption.
    + intros header MEMBER; apply HEADERS; cbn; apply in_or_app; right; exact MEMBER.
    + apply IHRECEIPT1 with (headers:=headers); try assumption.
      intros header MEMBER; apply HEADERS; cbn; apply in_or_app; left; exact MEMBER.
  - intros header MEMBER; eapply double_tree_captured_cache_interval; [apply FRESH; exact MEMBER| |exact H2|exact H3|apply ENV; exact MEMBER].
    apply DISTINCT; [exact MEMBER|apply HEADERS; cbn; left; reflexivity].
  - intros header MEMBER; eapply double_tree_captured_cache_interval; [apply FRESH; exact MEMBER| |exact H2|exact H3|apply ENV; exact MEMBER].
    apply DISTINCT; [exact MEMBER|apply HEADERS; cbn; left; reflexivity].
  - apply IHRECEIPT with (headers:=headers); try assumption.
    + intros header MEMBER; apply HEADERS; cbn; right; exact MEMBER.
    + intros header MEMBER; eapply double_tree_captured_cache_interval; [apply FRESH; exact MEMBER| |exact H2|exact H3|apply ENV; exact MEMBER].
      apply DISTINCT; [exact MEMBER|apply HEADERS; cbn; left; reflexivity].
Qed.

Print Assumptions double_tree_initialization_preserves_zero.
Print Assumptions double_tree_initialized_zero.
Print Assumptions double_tree_initialized_environment.
Print Assumptions double_tree_captured_cache_interval.
Print Assumptions double_tree_capture_environment_preserved.
