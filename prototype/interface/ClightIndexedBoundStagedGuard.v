From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightPureExpr ClightNoWrap ClightMatrixGuard
  ClightRedundantSet ClightStraightLine ClightLoopSyntax ClightLoopExecution ClightCountedLoop ClightRegionProgress.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyLoadedTreeSynthesis ClightQuietDeterminacy
  ClightLoopBridge ClightIndexedLoadBody ClightIndexedBoundSyntax ClightIndexedBoundPrefix ClightIndexedBoundScan
  ClightIndexedBoundGuard ClightIndexedPrefixScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition indexed_bound_setup iterator bound cap :=
  Test (register_guard iterator Int.zero)
    (Test (indexed_bound_active_expr bound 0)
      (Test (indexed_bound_limit_expr bound cap) (Decision true) (Decision false)) (Decision false)) (Decision false).
Definition indexed_bound_setup_accept iterator bound cap entry :=
  register_flag iterator Int.zero entry && indexed_bound_active_flag bound 0 entry && indexed_bound_limit_flag bound cap entry.
Definition indexed_bound_setup_property iterator bound cap entry :=
  register_equals iterator Int.zero tt entry /\ 0 < Int.signed (indexed_bound_word bound entry) <= Z.of_nat cap.

Lemma indexed_bound_setup_run iterator bound body cap entry : Z.of_nat cap <= Int.max_signed ->
  indexed_bound_domain iterator bound body entry ->
  decision_run entry (indexed_bound_setup iterator bound cap) (indexed_bound_setup_accept iterator bound cap entry).
Proof.
  intros CAP [[word [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE].
  unfold indexed_bound_setup, indexed_bound_setup_accept.
  eapply run_test; [apply register_expression_test; exists word; exact ITER|].
  destruct (register_flag iterator Int.zero entry); cbn; [|constructor].
  eapply run_test; [eapply indexed_bound_active_test;
    [change (-2147483648 <= 0 <= 2147483647); lia|exact BOUND|exact READ]|].
  destruct (indexed_bound_active_flag bound 0 entry); cbn; [|constructor].
  eapply run_test; [eapply indexed_bound_limit_test; [exact CAP|exact BOUND|exact READ]|].
  destruct (indexed_bound_limit_flag bound cap entry); constructor.
Qed.

Lemma indexed_bound_setup_sound iterator bound body cap entry :
  indexed_bound_domain iterator bound body entry -> indexed_bound_setup_accept iterator bound cap entry = true ->
  indexed_bound_setup_property iterator bound cap entry.
Proof.
  intros [[word [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE] ACCEPT.
  unfold indexed_bound_setup_accept in ACCEPT; repeat rewrite andb_true_iff in ACCEPT.
  destruct ACCEPT as [[ZERO ACTIVE] LIMIT]; split.
  - apply register_flag_evidence; [exists word; exact ITER|exact ZERO].
  - unfold indexed_bound_active_flag in ACTIVE; apply Z.ltb_lt in ACTIVE.
    unfold indexed_bound_limit_flag in LIMIT; apply Z.leb_le in LIMIT; lia.
Qed.

Definition indexed_bound_setup_condition fe O (observe : fragment_observation -> O -> Prop) iterator bound body cap
  (CAP : Z.of_nat cap <= Int.max_signed) :
  readonly_condition (readonly_clight_host fe observe) (indexed_bound_domain iterator bound body)
    (indexed_bound_setup_property iterator bound cap) (indexed_bound_setup iterator bound cap).
Proof.
  constructor.
  - intros entry DOMAIN; apply readonly_decision_run_safe with (answer := indexed_bound_setup_accept iterator bound cap entry).
    exact (@indexed_bound_setup_run iterator bound body cap entry CAP DOMAIN).
  - intros entry DOMAIN; exists (indexed_bound_setup_accept iterator bound cap entry), entry; split; [|reflexivity].
    exact (@indexed_bound_setup_run iterator bound body cap entry CAP DOMAIN).
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    apply (@indexed_bound_setup_sound iterator bound body cap entry DOMAIN).
    eapply readonly_decision_determinate; [exact (@indexed_bound_setup_run iterator bound body cap entry CAP DOMAIN)|exact RUN].
Defined.

Lemma indexed_bound_initial_prefix fe iterator out bound body cap entry :
  flatten_region body = [indexed_bound_body out iterator] ->
  indexed_bound_domain iterator bound body entry -> indexed_bound_setup_property iterator bound cap entry ->
  indexed_prefix_invariant fe iterator out bound body 0 entry.
Proof.
  intros FLAT [[word [upper [q [qofs [ITER [BOUND READ]]]]]] [observed COMPLETE]] [ZERO RANGE].
  unfold indexed_bound_word in RANGE; rewrite BOUND, READ in RANGE.
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  cbn [entry_temps entry_memory] in ZERO, ITER, BOUND, READ.
  pose proof (COMPLETE fe) as SOURCE.
  assert (QUIET : quiet_statement (indexed_bound_loop iterator bound body) = true).
  { cbn [indexed_bound_loop ClightStrictLoopProgress.strict_frontend_loop quiet_statement counter_increment].
    rewrite (@indexed_bound_body_quiet out iterator body FLAT); reflexivity. }
  pose proof (@quiet_execution_silent fe ge locals le memory _ trace after final outcome SOURCE QUIET) as SILENT.
  pose proof (@quiet_loop_normal fe ge locals le memory _ _ trace after final outcome QUIET SOURCE) as NORMAL;
    subst trace outcome.
  destruct (@indexed_bound_source_step fe ge locals iterator bound out body le memory after final 0 upper q qofs
    FLAT ltac:(lia) ZERO BOUND READ SOURCE) as [block [base [value [next_memory [OUT [STORE TAIL]]]]]].
  split; [change (0 <= 0 <= 2147483647); lia|].
  exists upper, q, qofs, block, base, le, memory, after, final.
  split; [exact OUT|split; [exact BOUND|split; [exact READ|split; [exact OUT|split; [exact BOUND|]]]]].
  split; [exact ZERO|split; [exact READ|split; [intros; assumption|exact SOURCE]]].
Qed.

Definition indexed_bound_prefix_condition fe O (observe : fragment_observation -> O -> Prop)
  iterator out bound body cap (IO : iterator <> out) (IQ : iterator <> bound)
  (FLAT : flatten_region body = [indexed_bound_body out iterator]) (CAP : Z.of_nat cap <= Int.max_signed) :
  readonly_condition (readonly_clight_host fe observe) (indexed_bound_domain iterator bound body)
    (indexed_bound_guard_property iterator out bound cap tt) (indexed_bound_guard_tree iterator out bound cap).
Proof.
  change (readonly_condition (readonly_clight_host fe observe) (indexed_bound_domain iterator bound body)
    (indexed_bound_guard_property iterator out bound cap tt)
    (decision_bind (indexed_bound_setup iterator bound cap) (indexed_bound_alias_scan out bound cap 0) (Decision false))).
  eapply readonly_condition_entails.
  - eapply sequence_readonly_conditions with (A := clight_readonly_check_algebra fe observe).
    + exact (@indexed_bound_setup_condition fe O observe iterator bound body cap CAP).
    + eapply readonly_condition_restrict.
      * exact (@indexed_prefix_scan_condition fe O observe iterator out bound body IO IQ FLAT cap 0).
      * intros entry [DOMAIN SETUP]; exact (@indexed_bound_initial_prefix fe iterator out bound body cap entry FLAT DOMAIN SETUP).
  - intros entry DOMAIN [[ZERO RANGE] SCAN]; unfold indexed_bound_guard_property.
    split; [exact ZERO|split; [exact RANGE|]].
    intros k ACTIVE; eapply indexed_prefix_scan_sound; [exact SCAN|cbn; lia|lia].
Defined.

(** Actual executable generation, not only a certificate about the legacy
    tree. The fixed host parameters are erased proof data: the syntax theorem
    and condition below apply to every actual caller semantics/observation. *)
Definition indexed_bound_generated_tree iterator out bound body cap
  (IO : iterator <> out) (IQ : iterator <> bound) (FLAT : flatten_region body = [indexed_bound_body out iterator]) :=
  decision_bind (indexed_bound_setup iterator bound cap)
    (synthesize_prefix_scan (clight_readonly_check_algebra (adapter_entry true) (@eq fragment_observation))
      (ClightReadonlyBranching.clight_readonly_branch_algebra (adapter_entry true) (@eq fragment_observation))
      (@indexed_prefix_spec (adapter_entry true) fragment_observation (@eq fragment_observation)
        iterator out bound body IO IQ FLAT) cap 0) (Decision false).

Lemma indexed_bound_generated_syntax iterator out bound body cap IO IQ FLAT :
  @indexed_bound_generated_tree iterator out bound body cap IO IQ FLAT = indexed_bound_guard_tree iterator out bound cap.
Proof. unfold indexed_bound_generated_tree; rewrite indexed_prefix_syntax; reflexivity. Qed.

Definition indexed_bound_generated_condition fe O (observe : fragment_observation -> O -> Prop)
  iterator out bound body cap IO IQ FLAT (CAP : Z.of_nat cap <= Int.max_signed) :
  readonly_condition (readonly_clight_host fe observe) (indexed_bound_domain iterator bound body)
    (indexed_bound_guard_property iterator out bound cap tt)
    (@indexed_bound_generated_tree iterator out bound body cap IO IQ FLAT).
Proof. rewrite indexed_bound_generated_syntax.
  exact (@indexed_bound_prefix_condition fe O observe iterator out bound body cap IO IQ FLAT CAP). Defined.

Print Assumptions indexed_bound_setup_condition.
Print Assumptions indexed_bound_initial_prefix.
Print Assumptions indexed_bound_prefix_condition.
Print Assumptions indexed_bound_generated_syntax.
Print Assumptions indexed_bound_generated_condition.
