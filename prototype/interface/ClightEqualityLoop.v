From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightNoWrap ClightPureExpr
  ClightRedundantSet ClightMatrixGuard ClightRectangularGuard ClightPositiveCheck ClightDecisionRule
  ClightCountedProtocol ClightFiniteRegion ClightRegionProgress ClightLoopExecution ClightStripmineLoops.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeSynthesis
  ClightCounterProgress ClightCircularCounter ClightCounterCondition ClightStableLoopCondition.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition equality_domain iterator bound entry := register_domain iterator entry /\ register_domain bound entry.
Definition equality_property iterator bound (_ : unit) entry :=
  register_equals iterator Int.zero tt entry /\ 0 < Int.signed (temp_word bound (entry_temps entry)).
Definition equality_positive_expression bound :=
  Ebinop Olt (Econst_int Int.zero type_int32s) (signed_word_view bound) type_int32s.
Lemma equality_positive_test bound entry : register_domain bound entry ->
  expression_test (equality_positive_expression bound) entry (register_positive bound entry).
Proof.
  intros [word LOOKUP]; destruct entry as [ge locals le memory].
  exists (Val.of_bool (Int.lt Int.zero word)); split.
  - eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vint word);
      [constructor|apply signed_word_view_evaluation; exact LOOKUP|reflexivity].
  - unfold register_positive, temp_word; rewrite LOOKUP; apply bool_of_bool.
Qed.
Definition equality_guard iterator bound := Test (register_guard iterator Int.zero)
  (Test (equality_positive_expression bound) (Decision true) (Decision false)) (Decision false).
Definition equality_accept iterator bound (_ : unit) entry :=
  register_flag iterator Int.zero entry && register_positive bound entry.
Lemma equality_guard_run iterator bound entry : equality_domain iterator bound entry ->
  decision_run entry (equality_guard iterator bound) (equality_accept iterator bound tt entry).
Proof.
  intros [ITER BOUND]; unfold equality_guard, equality_accept.
  eapply run_test; [apply register_expression_test; exact ITER|].
  destruct (register_flag iterator Int.zero entry); cbn; [|constructor].
  eapply run_test; [apply equality_positive_test; exact BOUND|].
  destruct (register_positive bound entry); constructor.
Qed.
Lemma equality_accept_sound iterator bound a entry : equality_domain iterator bound entry ->
  equality_accept iterator bound a entry = true -> equality_property iterator bound a entry.
Proof.
  intros [ITER BOUND] ACCEPT; unfold equality_accept in ACCEPT; apply andb_true_iff in ACCEPT as [ZERO POS].
  split; [apply register_flag_evidence; assumption|apply register_positive_sound; exact POS].
Qed.
Definition equality_dimension iterator bound :=
  @positive_dimension clight_entry unit (equality_domain iterator bound)
    (equality_property iterator bound) (equality_accept iterator bound) (@equality_accept_sound iterator bound).
Definition equality_primitives iterator bound :=
  @positive_tree_primitives unit (equality_domain iterator bound) (equality_property iterator bound)
    (equality_accept iterator bound) (@equality_accept_sound iterator bound)
    (fun _ => equality_guard iterator bound) (fun _ => ltac:(repeat constructor))
    (fun a entry DOMAIN => match a with tt => equality_guard_run DOMAIN end).
Definition equality_condition fe O (observe : fragment_observation -> O -> Prop) iterator bound :
  readonly_condition (readonly_clight_host fe observe) (equality_domain iterator bound)
    (equality_property iterator bound tt)
    (synthesize_decision_tree (equality_primitives iterator bound) (Fact tt)).
Proof.
  change (readonly_condition (readonly_clight_host fe observe) (equality_domain iterator bound)
    (fun entry => formula_property (atom_property (equality_dimension iterator bound)) (Fact tt) entry)
    (synthesize_decision_tree (equality_primitives iterator bound) (Fact tt))).
  apply synthesized_scalar_tree_condition with (D := equality_dimension iterator bound);
    intros []; cbn [equality_primitives positive_tree_primitives]; repeat constructor.
Defined.

Definition equality_header_invariant iterator bound upper (le : temp_env) (_ : mem) :=
  exists word, le ! iterator = Some (Vint word) /\ le ! bound = Some (Vint upper) /\
    0 <= Int.signed word <= Int.signed upper.
Definition equality_step_invariant iterator bound upper (le : temp_env) (memory : mem) :=
  equality_header_invariant iterator bound upper le memory /\ circular_active iterator bound le.
Lemma equality_header_transport ge locals le memory iterator bound upper flag :
  equality_header_invariant iterator bound upper le memory ->
  expression_test (unsigned_equality_test iterator bound) (Entry ge locals le memory) flag ->
  expression_test (unsigned_order_test iterator bound) (Entry ge locals le memory) flag.
Proof.
  intros [word [ITER [BOUND RANGE]]] TEST.
  destruct (unsigned_equality_test_facts TEST) as [word' [upper' [ITER' [BOUND' FLAG]]]].
  rewrite ITER in ITER'; injection ITER' as SAME; subst word'.
  rewrite BOUND in BOUND'; injection BOUND' as SAME; subst upper'.
  assert (BOOL : negb (Int.eq word upper) = Int.lt word upper).
  { pose proof (Int.eq_spec word upper) as EQ.
    unfold Int.lt; destruct (Int.eq word upper) eqn:SAME; destruct (zlt (Int.signed word) (Int.signed upper));
      cbn in *; try congruence.
    - subst word; lia.
    - exfalso; apply EQ; rewrite <- (Int.repr_signed word), <- (Int.repr_signed upper); f_equal; lia. }
  rewrite FLAG, BOOL; apply unsigned_order_test_eval; assumption.
Qed.
Lemma equality_domain_from_source fe ge locals iterator bound body le memory trace after final outcome :
  exec_stmt fe ge locals le memory (unsigned_equality_loop iterator bound body) trace after final outcome ->
  equality_domain iterator bound (Entry ge locals le memory).
Proof.
  intro SOURCE; unfold unsigned_equality_loop, generic_frontend_loop in SOURCE; inversion SOURCE; subst.
  all: match goal with HEAD : exec_stmt _ _ _ _ _ (Ssequence (Ssequence Sskip _) _) _ _ _ _ |- _ =>
    destruct (strict_header_execution HEAD) as [flag [TEST BRANCH]] end.
  all: destruct (unsigned_equality_test_facts TEST) as [word [upper [ITER [BOUND FLAG]]]];
    split; [exists word; exact ITER|exists upper; exact BOUND].
Qed.
Lemma equality_loop_quiet iterator bound body : memory_body body = true ->
  quiet_statement (unsigned_equality_loop iterator bound body) = true /\
  quiet_statement (unsigned_order_loop iterator bound body) = true.
Proof.
  intro BODY; assert (QUIET : quiet_statement body = true)
    by (apply finite_statement_quiet, memory_body_finite; exact BODY).
  unfold unsigned_equality_loop, unsigned_order_loop, generic_frontend_loop;
    cbn [quiet_statement]; rewrite QUIET; split; reflexivity.
Qed.
Theorem equality_loop_forward fe iterator bound body entry observed
  (DISTINCT : iterator <> bound) (BODY : memory_body body = true) :
  equality_domain iterator bound entry -> equality_property iterator bound tt entry ->
  clight_fragment_run fe (unsigned_equality_loop iterator bound body) entry observed ->
  clight_fragment_run fe (unsigned_order_loop iterator bound body) entry observed.
Proof.
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  intros [ITER [upper BOUND]] [ZERO POS] SOURCE.
  cbn [entry_temps] in *; unfold temp_word in POS; rewrite BOUND in POS.
  assert (INITIAL : equality_header_invariant iterator bound upper le memory).
  { exists Int.zero; split; [exact ZERO|split; [exact BOUND|rewrite Int.signed_zero; lia]]. }
  unfold clight_fragment_run in *; cbn in *.
  unfold unsigned_equality_loop in SOURCE; unfold unsigned_order_loop.
  unshelve eapply (proj1 (@generic_active_condition_transport fe ge locals iterator (unsigned_increment_expression iterator)
    (unsigned_equality_test iterator bound) (unsigned_order_test iterator bound) body
    (equality_header_invariant iterator bound upper) (equality_step_invariant iterator bound upper)
    _ _ _ _ le memory trace after final outcome SOURCE INITIAL)).
  - intros; eapply equality_header_transport; eassumption.
  - intros before mem events exit mem' out INV TEST RUN.
    pose proof (memory_body_temporaries_exact (@memory_body_writes_empty body BODY) RUN) as TEMPS; subst exit.
    split; [exact INV|].
    destruct (unsigned_equality_test_facts TEST) as [word [target [I [N EQ]]]].
    symmetry in EQ; apply negb_true_iff in EQ.
    exists word, target; split; [exact I|split; [exact N|]].
    pose proof (Int.eq_spec word target); rewrite EQ in H; exact H.
  - intros before mem [INV _]; exact INV.
  - intros before mem events exit mem' out [[word [I [N RANGE]]] ACTIVE] RUN.
    destruct (@unsigned_increment_execution_exact fe ge locals iterator bound before mem events exit mem' out
      DISTINCT ACTIVE RUN) as [SILENT [TEMPS [MEMORY OUTCOME]]]; subst.
    assert (DIFFERENT : word <> upper).
    { destruct ACTIVE as [word' [upper' [I' [N' NE]]]]; rewrite I in I'; rewrite N in N';
        injection I' as SAME; injection N' as SAME'; subst; exact NE. }
    assert (LT : Int.signed word < Int.signed upper).
    { destruct (zeq (Int.signed word) (Int.signed upper)); [exfalso; apply DIFFERENT;
        rewrite <- (Int.repr_signed word), <- (Int.repr_signed upper); f_equal; assumption|lia]. }
    exists (Int.add word Int.one); unfold increment_temps; rewrite I;
      split; [apply PTree.gss|split; [rewrite PTree.gso by congruence; exact N|]].
    rewrite Int.add_signed; change (Int.signed Int.one) with 1;
      rewrite Int.signed_repr by (pose proof (Int.signed_range upper); pose proof (Int.signed_range word); lia); lia.
Qed.
Print Assumptions equality_guard_run.
Print Assumptions equality_condition.
Print Assumptions equality_header_transport.
Print Assumptions equality_domain_from_source.
Print Assumptions equality_loop_forward.
