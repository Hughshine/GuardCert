From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightNoWrap ClightSameAddress
  ClightRegionProgress ClightMatrixGuard ClightRedundantSet ClightPositiveCheck ClightDecisionRule ClightPureExpr ClightCountedLoop ClightFrontendRegion
  ClightLoopExecution ClightLoopSyntax ClightStraightLine ClightTempFrame.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyLoadedTreeSynthesis
  ClightQuietDeterminacy ClightReadonlyCellSwap ClightStableLoadGuard ClightLoadedBoundSyntax ClightStableLoopCondition
  ReadonlyConditionComposition ClightConditionComposition.
Import ListNotations.
Set Implicit Arguments.

Definition loaded_bound_entry iterator parameter entry := exists x upper block offset,
  (entry_temps entry) ! iterator = Some (Vint x) /\
  (entry_temps entry) ! parameter = Some (Vptr block offset) /\
  Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) = Some (Vint upper).
Definition loaded_bound_domain iterator out parameter entry :=
  loaded_bound_entry iterator parameter entry /\
  (register_equals iterator Int.zero tt entry ->
    expression_test (loaded_bound_test iterator parameter) entry true -> address_domain out parameter entry).
Definition loaded_bound_property iterator out parameter (_ : unit) entry :=
  register_equals iterator Int.zero tt entry /\
  expression_test (loaded_bound_test iterator parameter) entry true /\ cell_pair_apart out parameter entry.
Definition loaded_bound_flag iterator parameter entry :=
  match (entry_temps entry) ! iterator, (entry_temps entry) ! parameter with
  | Some (Vint x), Some (Vptr b ofs) =>
    match Mem.loadv Mint32 (entry_memory entry) (Vptr b ofs) with
    | Some (Vint upper) => Int.lt x upper
    | _ => false end
  | _, _ => false end.
Definition loaded_bound_accept iterator out parameter (_ : unit) entry :=
  register_flag iterator Int.zero entry && loaded_bound_flag iterator parameter entry &&
    negb (address_accept out parameter entry).
Definition loaded_bound_guard iterator out parameter :=
  Test (register_guard iterator Int.zero)
    (Test (loaded_bound_test iterator parameter)
      (Test (same_address_guard out parameter) (Decision false) (Decision true)) (Decision false))
    (Decision false).

Lemma loaded_bound_entry_test iterator parameter entry : loaded_bound_entry iterator parameter entry ->
  expression_test (loaded_bound_test iterator parameter) entry (loaded_bound_flag iterator parameter entry).
Proof.
  intros [x [upper [b [ofs [I [Q READ]]]]]]; unfold loaded_bound_flag; rewrite I, Q, READ.
  destruct entry; eapply loaded_bound_test_eval; eassumption.
Qed.

Lemma loaded_bound_guard_run iterator out parameter entry : loaded_bound_domain iterator out parameter entry ->
  decision_run entry (loaded_bound_guard iterator out parameter)
    (loaded_bound_accept iterator out parameter tt entry).
Proof.
  intros [DOMAIN ADDRESSES]; destruct DOMAIN as [x [upper [b [ofs [I [Q READ]]]]]].
  assert (I_DOMAIN : register_domain iterator entry) by (exists x; exact I).
  assert (TEST : expression_test (loaded_bound_test iterator parameter) entry
    (loaded_bound_flag iterator parameter entry)) by (apply loaded_bound_entry_test; do 4 eexists; eauto).
  unfold loaded_bound_guard, loaded_bound_accept.
  eapply run_test; [apply register_expression_test; exact I_DOMAIN|].
  destruct (register_flag iterator Int.zero entry) eqn:ZERO; cbn; [|constructor].
  eapply run_test; [exact TEST|].
  destruct (loaded_bound_flag iterator parameter entry) eqn:ACTIVE; cbn; [|constructor].
  eapply run_test.
  - apply (proj2 (@address_guard_correct out parameter entry _
      (ADDRESSES (register_flag_evidence Int.zero I_DOMAIN ZERO) TEST))); reflexivity.
  - destruct (address_accept out parameter entry); constructor.
Qed.

Lemma loaded_bound_guard_sound iterator out parameter a entry : loaded_bound_domain iterator out parameter entry ->
  loaded_bound_accept iterator out parameter a entry = true -> loaded_bound_property iterator out parameter a entry.
Proof.
  intros [DOMAIN ADDRESSES] ACCEPT; destruct DOMAIN as [x [upper [b [ofs [I [Q READ]]]]]].
  assert (I_DOMAIN : register_domain iterator entry) by (exists x; exact I).
  unfold loaded_bound_accept in ACCEPT; apply andb_true_iff in ACCEPT as [PREFIX APART];
    apply andb_true_iff in PREFIX as [ZERO ACTIVE].
  pose proof (register_flag_evidence Int.zero I_DOMAIN ZERO) as ITER.
  assert (TEST : expression_test (loaded_bound_test iterator parameter) entry true).
  { rewrite <- ACTIVE; apply loaded_bound_entry_test; do 4 eexists; eauto. }
  split; [exact ITER|split; [exact TEST|]].
  apply stable_addresses_apart; [exact (ADDRESSES ITER TEST)|exact APART].
Qed.

Definition loaded_bound_dimension iterator out parameter :=
  @positive_dimension clight_entry unit (loaded_bound_domain iterator out parameter)
    (loaded_bound_property iterator out parameter) (loaded_bound_accept iterator out parameter)
    (@loaded_bound_guard_sound iterator out parameter).
Definition loaded_bound_primitives iterator out parameter :
  check_primitives decision_test_language (loaded_bound_domain iterator out parameter)
    (decide_atom (loaded_bound_dimension iterator out parameter)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language (loaded_bound_domain iterator out parameter)
    (decide_atom (loaded_bound_dimension iterator out parameter))
    (fun _ => loaded_bound_guard iterator out parameter) (fun _ => Decision true) _ _).
  - intros [] entry accepted DOMAIN.
    cbn [loaded_bound_dimension positive_dimension decide_atom checked_valid].
    destruct (loaded_bound_accept iterator out parameter tt entry) eqn:ACCEPT; cbn;
      split; intro RUN.
    + pose proof (readonly_decision_determinate RUN (loaded_bound_guard_run DOMAIN)) as SAME;
        rewrite ACCEPT in SAME; exact SAME.
    + subst accepted; pose proof (loaded_bound_guard_run DOMAIN) as PATH; rewrite ACCEPT in PATH; exact PATH.
    + pose proof (readonly_decision_determinate RUN (loaded_bound_guard_run DOMAIN)) as SAME;
        rewrite ACCEPT in SAME; exact SAME.
    + subst accepted; pose proof (loaded_bound_guard_run DOMAIN) as PATH; rewrite ACCEPT in PATH; exact PATH.
  - intros [] entry accepted expected DOMAIN DECIDE.
    cbn [loaded_bound_dimension positive_dimension decide_atom] in DECIDE.
    destruct (loaded_bound_accept iterator out parameter tt entry); [|discriminate].
    injection DECIDE as SAME; subst expected.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst accepted; constructor].

Defined.
Definition loaded_bound_tail iterator out parameter :=
  Test (loaded_bound_test iterator parameter)
    (Test (same_address_guard out parameter) (Decision false) (Decision true)) (Decision false).
Definition loaded_bound_tail_accept iterator out parameter entry :=
  loaded_bound_flag iterator parameter entry && negb (address_accept out parameter entry).
Lemma loaded_bound_tail_run iterator out parameter entry :
  loaded_bound_domain iterator out parameter entry -> register_equals iterator Int.zero tt entry ->
  decision_run entry (loaded_bound_tail iterator out parameter) (loaded_bound_tail_accept iterator out parameter entry).
Proof.
  intros [ENTRY ADDRESSES] ZERO.
  pose proof (loaded_bound_entry_test ENTRY) as TEST.
  unfold loaded_bound_tail, loaded_bound_tail_accept; eapply run_test; [exact TEST|].
  destruct (loaded_bound_flag iterator parameter entry); cbn; [|constructor].
  eapply run_test.
  - apply (proj2 (@address_guard_correct out parameter entry _ (ADDRESSES ZERO TEST))); reflexivity.
  - destruct (address_accept out parameter entry); constructor.
Qed.
Definition loaded_bound_tail_condition fe O (observe : fragment_observation -> O -> Prop) iterator out parameter :
  readonly_condition (readonly_clight_host fe observe)
    (fun entry => loaded_bound_domain iterator out parameter entry /\ register_equals iterator Int.zero tt entry)
    (fun entry => expression_test (loaded_bound_test iterator parameter) entry true /\ cell_pair_apart out parameter entry)
    (loaded_bound_tail iterator out parameter).
Proof.
  constructor.
  - intros entry [DOMAIN ZERO]; eapply readonly_decision_run_safe; apply loaded_bound_tail_run; assumption.
  - intros entry [DOMAIN ZERO]; exists (loaded_bound_tail_accept iterator out parameter entry), entry;
      split; [apply loaded_bound_tail_run; assumption|reflexivity].
  - intros entry answer checked [DOMAIN ZERO] [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    pose proof (readonly_decision_determinate RUN (@loaded_bound_tail_run iterator out parameter entry DOMAIN ZERO)) as ACCEPTED.
    unfold loaded_bound_tail_accept in ACCEPTED; symmetry in ACCEPTED; apply andb_true_iff in ACCEPTED as [ACTIVE APART].
    destruct DOMAIN as [ENTRY ADDRESSES]; pose proof (loaded_bound_entry_test ENTRY) as TEST;
      rewrite ACTIVE in TEST; split; [exact TEST|].
    apply stable_addresses_apart; [exact (ADDRESSES ZERO TEST)|exact APART].
Defined.
Definition loaded_bound_condition fe O (observe : fragment_observation -> O -> Prop) iterator out parameter :
  readonly_condition (readonly_clight_host fe observe) (loaded_bound_domain iterator out parameter)
    (loaded_bound_property iterator out parameter tt)
    (synthesize_decision_tree (loaded_bound_primitives iterator out parameter) (Fact tt)).
Proof.
  change (readonly_condition (readonly_clight_host fe observe) (loaded_bound_domain iterator out parameter)
    (loaded_bound_property iterator out parameter tt)
    (decision_bind (loaded_bound_guard iterator out parameter) (Decision true) (Decision false))).
  rewrite decision_bind_identity.
  change (readonly_condition (readonly_clight_host fe observe) (loaded_bound_domain iterator out parameter)
    (fun entry => register_equals iterator Int.zero tt entry /\
      (expression_test (loaded_bound_test iterator parameter) entry true /\ cell_pair_apart out parameter entry))
    (then_check (clight_readonly_check_algebra fe observe)
      (Test (register_guard iterator Int.zero) (Decision true) (Decision false))
      (loaded_bound_tail iterator out parameter))).
  apply sequence_readonly_conditions.
  - apply readonly_expression_condition.
    + intros entry [[word [upper [b [ofs [ITER REST]]]]] ADDRESSES].
      exists (register_flag iterator Int.zero entry); apply register_expression_test; exists word; exact ITER.
    + intros entry [[word [upper [b [ofs [ITER REST]]]]] ADDRESSES] TEST.
      assert (DOMAIN : register_domain iterator entry) by (exists word; exact ITER).
      pose proof (@register_expression_test iterator Int.zero entry DOMAIN) as KNOWN.
      assert (FLAG : register_flag iterator Int.zero entry = true) by
        (eapply readonly_test_determinate; [exact KNOWN|exact TEST]).
      apply register_flag_evidence; assumption.
  - apply loaded_bound_tail_condition.
Defined.

Theorem loaded_bound_domain_from_source fe ge locals le memory iterator out parameter body after final :
  flatten_region body = [loaded_bound_body out iterator] ->
  exec_stmt fe ge locals le memory (loaded_bound_loop iterator parameter body) E0 after final Out_normal ->
  loaded_bound_domain iterator out parameter (Entry ge locals le memory).
Proof.
  intros FLAT SOURCE.
  assert (SOURCE_BODY_QUIET : quiet_statement body = true) by
    (apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]).
  assert (SOURCE_BODY_NORMAL : normal_statement body = true) by
    (apply flatten_normal_certificate; rewrite FLAT; constructor; [reflexivity|constructor]).
  unfold loaded_bound_loop, ClightStrictLoopProgress.strict_frontend_loop in SOURCE; inversion SOURCE; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Ssequence (Ssequence Sskip _) _) _ _ _ _ |- _ =>
    destruct (strict_header_execution HEADER) as [flag [TEST BRANCH]]
  end.
  all: split.
  all: try (destruct (loaded_bound_test_facts TEST) as [x [upper [b [ofs [I [Q [READ _]]]]]]];
    exists x, upper, b, ofs; repeat split; assumption).
  all: intros ZERO ACTIVE; pose proof (readonly_test_determinate TEST ACTIVE) as FLAG; subst flag; cbn in BRANCH.
  all: match type of BRANCH with exec_stmt _ _ _ _ _ ?actual_body ?tr ?exit ?mem ?outcome =>
      pose proof (@quiet_execution_silent fe ge locals le memory actual_body tr exit mem outcome
        BRANCH SOURCE_BODY_QUIET) as SILENT;
      pose proof (@normal_statement_execution fe ge locals actual_body SOURCE_BODY_NORMAL le memory tr exit mem outcome
        BRANCH) as EXIT
    end; subst.
  all: apply (flattened_singleton_execution FLAT) in BRANCH;
    destruct (loaded_bound_body_store BRANCH) as [p [po [value [P STORE]]]];
    destruct (loaded_bound_test_facts ACTIVE) as [x [upper [q [qo [I [Q [READ _]]]]]]].
  all: exists p, po, q, qo; repeat split; try assumption;
    [apply writable_word_valid_pointer; exact (proj1 (@storev_word_facts _ _ _ _ _ STORE))|
     eapply loaded_address_valid; exact READ].
Qed.
Print Assumptions loaded_bound_condition.
Print Assumptions loaded_bound_domain_from_source.
Print Assumptions loaded_bound_tail_run.
Print Assumptions loaded_bound_tail_condition.
