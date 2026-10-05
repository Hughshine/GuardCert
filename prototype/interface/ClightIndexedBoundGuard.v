From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr ClightNoWrap
  ClightDecisionRule ClightMatrixGuard ClightRedundantSet ClightLoopSyntax ClightLoopExecution ClightStraightLine
  ClightRegionProgress ClightCountedLoop.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyLoadedTreeSynthesis
  ClightLoopBridge ClightQuietDeterminacy ClightIndexedLoadBody ClightIndexedAliasGuard
  ClightIndexedBoundSyntax ClightIndexedBoundPrefix ClightIndexedBoundScan ClightStableLoopCondition.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition indexed_bound_entry iterator bound entry := exists word upper q qofs,
  (entry_temps entry) ! iterator = Some (Vint word) /\
  (entry_temps entry) ! bound = Some (Vptr q qofs) /\
  Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some (Vint upper).
Definition indexed_bound_domain iterator bound body entry :=
  indexed_bound_entry iterator bound entry /\ quiet_source_completion (indexed_bound_loop iterator bound body) entry.
Definition indexed_bound_limit_expr bound cap :=
  Ebinop Ole (indexed_bound_value bound) (Econst_int (Int.repr (Z.of_nat cap)) type_int32s) type_int32s.
Definition indexed_bound_limit_flag bound cap entry :=
  (Int.signed (indexed_bound_word bound entry) <=? Z.of_nat cap).
Definition indexed_bound_guard_tree iterator out bound cap :=
  Test (register_guard iterator Int.zero)
    (Test (indexed_bound_active_expr bound 0)
      (Test (indexed_bound_limit_expr bound cap)
        (indexed_bound_alias_scan out bound cap 0) (Decision false)) (Decision false)) (Decision false).
Definition indexed_bound_guard_accept iterator out bound cap (_ : unit) entry :=
  register_flag iterator Int.zero entry && indexed_bound_active_flag bound 0 entry &&
    indexed_bound_limit_flag bound cap entry && indexed_bound_alias_accept out bound cap 0 entry.
Definition indexed_bound_guard_property iterator out bound cap (_ : unit) entry :=
  register_equals iterator Int.zero tt entry /\
  0 < Int.signed (indexed_bound_word bound entry) <= Z.of_nat cap /\
  forall k, 0 <= k < Int.signed (indexed_bound_word bound entry) -> indexed_alias_flag out bound k entry = false.

Lemma indexed_bound_limit_test bound cap entry q qofs upper : Z.of_nat cap <= Int.max_signed ->
  (entry_temps entry) ! bound = Some (Vptr q qofs) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some (Vint upper) ->
  expression_test (indexed_bound_limit_expr bound cap) entry (indexed_bound_limit_flag bound cap entry).
Proof.
  intros CAP BOUND READ; unfold indexed_bound_limit_flag, indexed_bound_word; rewrite BOUND, READ.
  exists (Val.of_bool (Int.signed upper <=? Z.of_nat cap)); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1 := Vint upper) (v2 := Vint (Int.repr (Z.of_nat cap))).
  - eapply indexed_bound_value_evaluation; eassumption.
  - constructor.
  - change (Some (Val.of_bool (negb (Int.lt (Int.repr (Z.of_nat cap)) upper))) =
      Some (Val.of_bool (Int.signed upper <=? Z.of_nat cap))).
    unfold Int.lt; rewrite Int.signed_repr by
      (pose proof (Nat2Z.is_nonneg cap); change Int.min_signed with (-2147483648); lia).
    destruct (zlt (Z.of_nat cap) (Int.signed upper)) as [LT|GE].
    + assert (B : (Int.signed upper <=? Z.of_nat cap) = false) by (apply Z.leb_gt; lia); rewrite B; reflexivity.
    + assert (B : (Int.signed upper <=? Z.of_nat cap) = true) by (apply Z.leb_le; lia); rewrite B; reflexivity.
Qed.

Lemma indexed_bound_guard_run iterator out bound body cap entry :
  iterator <> out -> iterator <> bound -> flatten_region body = [indexed_bound_body out iterator] ->
  Z.of_nat cap <= Int.max_signed -> indexed_bound_domain iterator bound body entry ->
  decision_run entry (indexed_bound_guard_tree iterator out bound cap)
    (indexed_bound_guard_accept iterator out bound cap tt entry).
Proof.
  intros IO IQ FLAT CAP [[word [upper [q [qofs [ITER [BOUND READ]]]]]] [observed COMPLETE]].
  assert (I_DOMAIN : register_domain iterator entry) by (exists word; exact ITER).
  unfold indexed_bound_guard_tree, indexed_bound_guard_accept.
  eapply run_test; [apply register_expression_test; exact I_DOMAIN|].
  destruct (register_flag iterator Int.zero entry) eqn:ZERO; cbn; [|constructor].
  eapply run_test.
  - eapply indexed_bound_active_test; [change (-2147483648 <= 0 <= 2147483647); lia|exact BOUND|exact READ].
  - destruct (indexed_bound_active_flag bound 0 entry) eqn:ACTIVE; cbn; [|constructor].
    eapply run_test; [eapply indexed_bound_limit_test; [exact CAP|exact BOUND|exact READ]|].
    destruct (indexed_bound_limit_flag bound cap entry); cbn; [|constructor].
    pose proof (register_flag_evidence Int.zero I_DOMAIN ZERO) as I_ZERO.
    unfold indexed_bound_active_flag, indexed_bound_word in ACTIVE; rewrite BOUND, READ in ACTIVE; apply Z.ltb_lt in ACTIVE.
    destruct entry as [ge locals base_temps memory], observed as [trace after final outcome].
    cbn [entry_temps entry_memory] in BOUND, READ, I_ZERO.
    pose proof (COMPLETE (fun _ _ _ _ _ _ _ => False)) as SOURCE.
    assert (QUIET : quiet_statement (indexed_bound_loop iterator bound body) = true).
    { cbn [indexed_bound_loop ClightStrictLoopProgress.strict_frontend_loop quiet_statement counter_increment].
      rewrite (@indexed_bound_body_quiet out iterator body FLAT); reflexivity. }
    pose proof (@quiet_execution_silent _ ge locals base_temps memory _ trace after final outcome SOURCE QUIET) as SILENT.
    pose proof (@quiet_loop_normal _ ge locals base_temps memory _ _ trace after final outcome QUIET SOURCE) as NORMAL;
      subst trace outcome.
    destruct (@indexed_bound_source_step _ ge locals iterator bound out body base_temps memory after final 0 upper q qofs
      FLAT ltac:(lia) I_ZERO BOUND READ SOURCE) as [block [base [value [next_memory [OUT [STORE TAIL]]]]]].
    eapply indexed_bound_alias_scan_run; [exact IO|exact IQ|exact FLAT|lia|cbn; exact CAP|
      exact OUT|exact BOUND|exact READ|exact OUT|exact BOUND|exact I_ZERO|exact READ| |exact SOURCE].
    intros b ofs WORD; exact WORD.
Qed.

Lemma indexed_bound_guard_sound iterator out bound cap a entry :
  register_domain iterator entry ->
  indexed_bound_guard_accept iterator out bound cap a entry = true ->
  indexed_bound_guard_property iterator out bound cap a entry.
Proof.
  intros I_DOMAIN ACCEPT; unfold indexed_bound_guard_accept in ACCEPT; repeat rewrite andb_true_iff in ACCEPT.
  destruct ACCEPT as [[[ZERO ACTIVE] LIMIT] SCAN].
  unfold indexed_bound_guard_property; split.
  - apply register_flag_evidence; assumption.
  - unfold indexed_bound_active_flag in ACTIVE; apply Z.ltb_lt in ACTIVE.
    unfold indexed_bound_limit_flag in LIMIT; apply Z.leb_le in LIMIT.
    split; [lia|intros k RANGE; eapply indexed_bound_alias_scan_sound; [exact SCAN|cbn; lia|lia]].
Qed.
Definition indexed_bound_primitives iterator out bound body cap (IO : iterator <> out) (IQ : iterator <> bound)
  (FLAT : flatten_region body = [indexed_bound_body out iterator]) (CAP : Z.of_nat cap <= Int.max_signed) :=
  @positive_readonly_tree_primitives unit (indexed_bound_domain iterator bound body)
    (indexed_bound_guard_property iterator out bound cap) (indexed_bound_guard_accept iterator out bound cap)
    (fun a entry DOMAIN ACCEPT => @indexed_bound_guard_sound iterator out bound cap a entry
      ltac:(destruct DOMAIN as [[word [upper [q [qofs [ITER _]]]]] _]; exists word; exact ITER) ACCEPT)
    (fun _ => indexed_bound_guard_tree iterator out bound cap)
    (fun _ entry DOMAIN => @indexed_bound_guard_run iterator out bound body cap entry IO IQ FLAT CAP DOMAIN).
Definition indexed_bound_condition fe O (observe : fragment_observation -> O -> Prop)
  iterator out bound body cap IO IQ FLAT CAP :
  readonly_condition (readonly_clight_host fe observe) (indexed_bound_domain iterator bound body)
    (indexed_bound_guard_property iterator out bound cap tt)
    (synthesize_decision_tree (@indexed_bound_primitives iterator out bound body cap IO IQ FLAT CAP) (Fact tt)).
Proof.
  apply synthesized_loaded_tree_condition with
    (D := @positive_dimension clight_entry unit (indexed_bound_domain iterator bound body)
      (indexed_bound_guard_property iterator out bound cap) (indexed_bound_guard_accept iterator out bound cap)
      (fun a entry DOMAIN ACCEPT => @indexed_bound_guard_sound iterator out bound cap a entry
        ltac:(destruct DOMAIN as [[word [upper [q [qofs [ITER _]]]]] _]; exists word; exact ITER) ACCEPT))
    (premise := Fact tt).
Defined.

Theorem indexed_bound_domain_from_source fe ge locals le memory iterator bound out body after final :
  flatten_region body = [indexed_bound_body out iterator] ->
  exec_stmt fe ge locals le memory (indexed_bound_loop iterator bound body) E0 after final Out_normal ->
  indexed_bound_domain iterator bound body (Entry ge locals le memory).
Proof.
  intros FLAT SOURCE; split.
  - assert (FIRST : exists flag, expression_test (indexed_bound_test iterator bound) (Entry ge locals le memory) flag).
    { inversion SOURCE; subst.
      all: match goal with HEADER : exec_stmt _ _ _ _ _ (Ssequence (Ssequence Sskip _) _) _ _ _ _ |- _ =>
        destruct (strict_header_execution HEADER) as [flag [TEST _]]; exists flag; exact TEST end. }
    destruct FIRST as [flag TEST]; destruct (indexed_bound_test_facts TEST) as [word [upper [q [qofs [I [Q [READ _]]]]]]].
    exists word, upper, q, qofs; repeat split; assumption.
  - eapply quiet_source_completion_from_run with (observed := FragmentObservation E0 after final Out_normal); [|exact SOURCE].
    cbn [indexed_bound_loop ClightStrictLoopProgress.strict_frontend_loop quiet_statement counter_increment].
    rewrite (@indexed_bound_body_quiet out iterator body FLAT); reflexivity.
Qed.
Print Assumptions indexed_bound_guard_run.
Print Assumptions indexed_bound_guard_sound.
Print Assumptions indexed_bound_condition.
Print Assumptions indexed_bound_domain_from_source.
