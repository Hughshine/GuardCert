From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightSameAddress ClightCountedLoop ClightStraightLine.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching
  ReadonlyPrefixScan ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching
  ClightStableLoadBody ClightReadonlyLoadedTreeSynthesis ClightReadonlyCellSwap ClightIndexedLoadBody ClightIndexedAliasGuard
  ClightIndexedBoundSyntax ClightIndexedBoundPrefix ClightIndexedBoundScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The invariant contains a real remaining source execution and permissions
    transported back to the original entry. It contains no complete-footprint
    or future non-alias assumption. Its witness is erased from runtime code. *)
Definition indexed_prefix_invariant fe iterator out bound body point entry :=
  0 <= point <= Int.max_signed /\
  exists upper q qofs block base current_temps current_memory after final,
    (entry_temps entry) ! out = Some (Vptr block base) /\
    (entry_temps entry) ! bound = Some (Vptr q qofs) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some (Vint upper) /\
    current_temps ! out = Some (Vptr block base) /\
    current_temps ! bound = Some (Vptr q qofs) /\
    current_temps ! iterator = Some (Vint (Int.repr point)) /\
    Mem.loadv Mint32 current_memory (Vptr q qofs) = Some (Vint upper) /\
    (forall b ofs, writable_word current_memory b ofs -> writable_word (entry_memory entry) b ofs) /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current_temps current_memory
      (indexed_bound_loop iterator bound body) E0 after final Out_normal.
Definition indexed_prefix_active bound point entry := point < Int.signed (indexed_bound_word bound entry).
Definition indexed_prefix_active_probe bound point :=
  Test (indexed_bound_active_expr bound point) (Decision true) (Decision false).
Definition indexed_prefix_point_probe out bound point :=
  Test (indexed_alias_expr out bound point) (Decision false) (Decision true).

Lemma indexed_prefix_activity fe O (observe : fragment_observation -> O -> Prop) iterator out bound body point :
  readonly_classifier (readonly_clight_host fe observe)
    (indexed_prefix_invariant fe iterator out bound body point) (indexed_prefix_active bound point)
    (fun entry => ~ indexed_prefix_active bound point entry) (indexed_prefix_active_probe bound point).
Proof.
  unfold indexed_prefix_active_probe; apply readonly_expression_classifier.
  - intros entry [RANGE [upper [q [qofs [block [base [temps [memory [after [final
      [OUT [BOUND [READ REST]]]]]]]]]]]]].
    exists (indexed_bound_active_flag bound point entry); eapply indexed_bound_active_test;
      [unfold signed_range; change Int.min_signed with (-2147483648); lia|exact BOUND|exact READ].
  - intros entry [RANGE [upper [q [qofs [block [base [temps [memory [after [final
      [OUT [BOUND [READ REST]]]]]]]]]]]]] TEST.
    assert (VALUE : indexed_bound_active_flag bound point entry = true).
    { eapply readonly_test_determinate; [eapply indexed_bound_active_test;
        [unfold signed_range; change Int.min_signed with (-2147483648); lia|exact BOUND|exact READ]|exact TEST]. }
    unfold indexed_prefix_active, indexed_bound_active_flag in *; apply Z.ltb_lt; exact VALUE.
  - intros entry [RANGE [upper [q [qofs [block [base [temps [memory [after [final
      [OUT [BOUND [READ REST]]]]]]]]]]]]] TEST.
    assert (VALUE : indexed_bound_active_flag bound point entry = false).
    { eapply readonly_test_determinate; [eapply indexed_bound_active_test;
        [unfold signed_range; change Int.min_signed with (-2147483648); lia|exact BOUND|exact READ]|exact TEST]. }
    unfold indexed_prefix_active, indexed_bound_active_flag in *; apply Z.ltb_ge in VALUE; lia.
Defined.

Lemma indexed_prefix_point fe O (observe : fragment_observation -> O -> Prop) iterator out bound body point :
  iterator <> out -> iterator <> bound -> flatten_region body = [indexed_bound_body out iterator] ->
  readonly_condition (readonly_clight_host fe observe)
    (fun entry => indexed_prefix_invariant fe iterator out bound body point entry /\ indexed_prefix_active bound point entry)
    (fun entry => indexed_alias_flag out bound point entry = false /\
      indexed_prefix_invariant fe iterator out bound body (point+1) entry)
    (indexed_prefix_point_probe out bound point).
Proof.
  intros IO IQ FLAT.
  assert (READY : forall entry,
    indexed_prefix_invariant fe iterator out bound body point entry -> indexed_prefix_active bound point entry ->
    exists flag, expression_test (indexed_alias_expr out bound point) entry flag).
  { intros entry [RANGE [upper [q [qofs [block [base [temps [memory [after [final
      [OUT [BOUND [READ [CURRENT_OUT [CURRENT_BOUND [ITER [CURRENT_READ [PERMISSIONS SOURCE]]]]]]]]]]]]]]]]]] ACTIVE.
    unfold indexed_prefix_active, indexed_bound_word in ACTIVE; rewrite BOUND, READ in ACTIVE.
    destruct (@indexed_bound_source_step fe (entry_ge entry) (entry_env entry) iterator bound out body temps memory
      after final point upper q qofs FLAT ltac:(lia) ITER CURRENT_BOUND CURRENT_READ SOURCE)
      as [other [other_base [value [next_memory [POINTER [STORE TAIL]]]]]].
    assert (SAME : Vptr other other_base = Vptr block base) by congruence; injection SAME; intros; subst.
    destruct (@storev_word_facts _ _ _ _ _ STORE) as [WORD RAW].
    exists (indexed_alias_flag out bound point entry); eapply indexed_alias_test;
      [exact OUT|exact BOUND|exact READ|apply PERMISSIONS; exact WORD]. }
  constructor.
  - intros entry [INV ACTIVE]; cbn [indexed_prefix_point_probe readonly_tree_safe].
    split; [apply READY; assumption|intros answer RUN; destruct answer; exact I].
  - intros entry [INV ACTIVE]; destruct (READY entry INV ACTIVE) as [flag TEST].
    exists (negb flag), entry; split; [|reflexivity]; unfold indexed_prefix_point_probe.
    eapply run_test; [exact TEST|destruct flag; constructor].
  - intros entry answer checked [[RANGE [upper [q [qofs [block [base [temps [memory [after [final
      [OUT [BOUND [READ [CURRENT_OUT [CURRENT_BOUND [ITER [CURRENT_READ [PERMISSIONS SOURCE]]]]]]]]]]]]]]]]]] ACTIVE] [RUN SAME].
    split; [exact SAME|intro ACCEPT; subst answer].
    unfold indexed_prefix_active, indexed_bound_word in ACTIVE; rewrite BOUND, READ in ACTIVE.
    destruct (@indexed_bound_source_step fe (entry_ge entry) (entry_env entry) iterator bound out body temps memory
      after final point upper q qofs FLAT ltac:(lia) ITER CURRENT_BOUND CURRENT_READ SOURCE)
      as [other [other_base [value [next_memory [POINTER [STORE TAIL]]]]]].
    assert (SAME_PTR : Vptr other other_base = Vptr block base) by congruence; injection SAME_PTR; intros; subst.
    destruct (@storev_word_facts _ _ _ _ _ STORE) as [WORD RAW].
    assert (TEST : expression_test (indexed_alias_expr out bound point) entry (indexed_alias_flag out bound point entry)).
    { eapply indexed_alias_test; [exact OUT|exact BOUND|exact READ|apply PERMISSIONS; exact WORD]. }
    assert (APART : indexed_alias_flag out bound point entry = false).
    { unfold indexed_prefix_point_probe in RUN; inversion RUN; subst.
      match goal with LEAF : decision_run _ (if ?choice then Decision false else Decision true) true |- _ =>
        destruct choice; inversion LEAF; subst end.
      eapply readonly_test_determinate; eassumption. }
    split; [exact APART|].
    assert (NEXT_READ : Mem.loadv Mint32 next_memory (Vptr q qofs) = Some (Vint upper)).
    { eapply mint32_load_survives_apart_store; [exact STORE|exact CURRENT_READ|].
      exact (@indexed_alias_apart out bound point entry block base q qofs OUT BOUND APART). }
    split; [pose proof (Int.signed_range upper); lia|].
    exists upper, q, qofs, block, base,
      (PTree.set iterator (Vint (Int.repr (point+1))) temps), next_memory, after, final.
    split; [exact OUT|split; [exact BOUND|split; [exact READ|]]].
    split; [rewrite PTree.gso by congruence; exact CURRENT_OUT|].
    split; [rewrite PTree.gso by congruence; exact CURRENT_BOUND|].
    split; [apply PTree.gss|split; [exact NEXT_READ|split; [|exact TAIL]]].
    intros permission_block permission_offset [VALID ADDRESS]; apply PERMISSIONS; split; [|exact ADDRESS].
    eapply Mem.store_valid_access_2; [exact RAW|exact VALID].
Defined.

Definition indexed_prefix_spec fe O (observe : fragment_observation -> O -> Prop) iterator out bound body
  (IO : iterator <> out) (IQ : iterator <> bound) (FLAT : flatten_region body = [indexed_bound_body out iterator]) :
  readonly_prefix_spec (readonly_clight_host fe observe) Z :=
  @ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun point => point+1)
    (indexed_prefix_active_probe bound) (indexed_prefix_point_probe out bound)
    (indexed_prefix_invariant fe iterator out bound body) (indexed_prefix_active bound)
    (fun point entry => indexed_alias_flag out bound point entry = false)
    (@indexed_prefix_activity fe O observe iterator out bound body)
    (fun point => @indexed_prefix_point fe O observe iterator out bound body point IO IQ FLAT).

Lemma indexed_prefix_syntax fe O (observe : fragment_observation -> O -> Prop) iterator out bound body IO IQ FLAT fuel point :
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    (@indexed_prefix_spec fe O observe iterator out bound body IO IQ FLAT) fuel point =
  indexed_bound_alias_scan out bound fuel point.
Proof.
  revert point; induction fuel as [|fuel IH]; intro point; cbn [synthesize_prefix_scan indexed_bound_alias_scan
    indexed_prefix_spec indexed_prefix_active_probe indexed_prefix_point_probe clight_readonly_check_algebra
    clight_readonly_branch_algebra branch_check constant_check prefix_active_probe prefix_point_probe prefix_next decision_bind].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Definition indexed_prefix_scan_condition fe O (observe : fragment_observation -> O -> Prop) iterator out bound body
  IO IQ FLAT fuel point : readonly_condition (readonly_clight_host fe observe)
    (indexed_prefix_invariant fe iterator out bound body point)
    (prefix_scan_property (@indexed_prefix_spec fe O observe iterator out bound body IO IQ FLAT) fuel point)
    (indexed_bound_alias_scan out bound fuel point).
Proof. rewrite <- (@indexed_prefix_syntax fe O observe iterator out bound body IO IQ FLAT fuel point).
  exact (@synthesized_prefix_scan_condition clight_entry (readonly_clight_host fe observe) Z
    (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    (@indexed_prefix_spec fe O observe iterator out bound body IO IQ FLAT) fuel point). Defined.

Lemma indexed_prefix_scan_sound fe O (observe : fragment_observation -> O -> Prop) iterator out bound body IO IQ FLAT fuel point entry :
  prefix_scan_property (@indexed_prefix_spec fe O observe iterator out bound body IO IQ FLAT) fuel point entry ->
  forall k, point <= k < point + Z.of_nat fuel -> k < Int.signed (indexed_bound_word bound entry) ->
    indexed_alias_flag out bound k entry = false.
Proof.
  revert point; induction fuel as [|fuel IH]; intros point PROP k RANGE ACTIVE;
    cbn [prefix_scan_property indexed_prefix_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in RANGE; lia|].
  destruct (PROP ltac:(unfold indexed_prefix_active; lia)) as [APART NEXT].
  destruct (Z.eq_dec k point); [subst; exact APART|].
  eapply IH; [exact NEXT|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.

Print Assumptions indexed_prefix_activity.
Print Assumptions indexed_prefix_point.
Print Assumptions indexed_prefix_syntax.
Print Assumptions indexed_prefix_scan_condition.
Print Assumptions indexed_prefix_scan_sound.
