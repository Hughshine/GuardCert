From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightNoWrap
  ClightRedundantSet ClightTempFrame ClightTempFootprint ClightProjectedExecution ClightPrivateRegion ClightPrivateRule
  ClightCountedLoop ClightCountedProtocol ClightFramedLoop ClightFrontendLoopProtocol ClightFrontendRegion
  ClightZeroTrip ClightLoopExecution ClightLoopSyntax ClightParametricLoops CountedStripmine ClightStripmineLoops ClightStripmineGuard
  CompCertMemoryEquivalence.
Import ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma frontend_scope_parts live iterator bound body :
  statement_scope live (frontend_counted_loop iterator bound body) ->
  In iterator live /\ In bound live /\ statement_scope live body.
Proof.
  unfold statement_scope, frontend_counted_loop, counter_condition, counter_increment;
    cbn [statement_temps expression_temps]; intro SCOPE.
  repeat split.
  - apply SCOPE; cbn; auto.
  - apply SCOPE; cbn; auto.
  - intros id IN; apply SCOPE; cbn; right; right; apply in_or_app; auto.
Qed.
Lemma stripmine_source_domain fe ge locals le memory iterator bound body after final :
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
  stripmine_guard_domain iterator bound (Entry ge locals le memory).
Proof.
  intro RUN; destruct (frontend_entry_test RUN) as [flag TEST].
  destruct (@counter_test_domain iterator bound (Entry ge locals le memory) flag TEST)
    as [i [n [I N]]]; split; [exists i; exact I|exists n; exact N].
Qed.

Section RULE.
Variable live : list ident.
Variable iterator bound limit : ident.
Variable width : nat.
Variable body : statement.
Hypothesis DISTINCT : iterator <> bound.
Hypothesis PRIVATE : ~ In limit live.
Hypothesis WIDTH : 0 < Z.of_nat width <= Int.max_signed.
Hypothesis BODY : memory_body body = true.

Theorem stripmine_local fe ge locals le memory le' final upper :
  statement_scope live (frontend_counted_loop iterator bound body) ->
  le ! iterator = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr upper)) ->
  0 < upper <= stripmine_bound_limit width ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound body) E0 le' final Out_normal ->
  exists target, exec_stmt fe ge locals le memory (stripmine_loop iterator bound limit width body) E0 target final Out_normal /\
    temp_agree live le' target.
Proof.
  intros SCOPE ZERO BOUND RANGE RUN.
  destruct (frontend_scope_parts SCOPE) as [ILIVE [BLIVE BODY_SCOPE]].
  assert (IL : iterator <> limit) by (intro SAME; subst limit; contradiction).
  assert (BL : bound <> limit) by (intro SAME; subst limit; contradiction).
  assert (WRITES := @memory_body_writes_empty body BODY).
  assert (NORMAL := @memory_body_normal body BODY).
  set (stable := temp_except live iterator).
  set (point := canonical_body fe ge locals iterator body le).
  set (count := Z.to_nat upper).
  assert (LENGTH : upper = Z.of_nat count) by (unfold count; rewrite Z2Nat.id; lia).
  assert (UR : signed_range upper) by (unfold signed_range, stripmine_bound_limit in *; change Int.min_signed with (-2147483648); lia).
  assert (ZR : signed_range 0) by (change (-2147483648 <= 0 <= 2147483647); lia).
  assert (DECODE : forall x temps before after memory', 0 <= x < upper ->
    temps ! iterator = Some (Vint (Int.repr x)) -> temps ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable le temps -> exec_stmt fe ge locals temps before body E0 after memory' Out_normal ->
    point x before memory' /\ after = loop_settle None temps).
  { intros x temps before after memory' X I N F EXEC.
    exact (@canonical_body_decode fe ge locals live iterator body le WRITES BODY_SCOPE x temps before after memory' I F EXEC). }
  destruct (@frontend_parametric_decode fe ge locals iterator bound body None point 0 upper stable le
    DISTINCT ltac:(split; intro BAD; inversion BAD) (temp_except_iterator live iterator)
    ltac:(intros id MEMBER BAD; inversion BAD) NORMAL WRITES UR DECODE
    count 0 le memory le' final ltac:(lia) ZR ltac:(lia) ZERO BOUND (temp_agree_refl stable le) RUN) as [ITER EXIT].
  assert (POS : (0 < width)%nat) by lia.
  pose proof (@counted_iterations_stripmine mem point width POS count 0 memory final ITER) as CHUNKS.
  destruct (@stripmine_chunked_encode fe ge locals live iterator bound limit width body le upper
    DISTINCT IL BL PRIVATE POS ltac:(unfold stripmine_bound_limit in RANGE; lia) WRITES BODY_SCOPE
    count 0 memory final CHUNKS le ltac:(lia) ltac:(lia) ZERO BOUND (temp_agree_refl stable le)) as [target [EXEC [TI TF]]].
  exists target; split; [exact EXEC|].
  rewrite EXIT; unfold loop_exit, loop_settle; destruct count;
    exact (@canonical_temp_agreement live iterator le target (Vint (Int.repr upper)) TI TF).
Qed.

Definition stripmine_region_rule : encoded_private_rule live (frontend_counted_loop iterator bound body)
  (stripmine_loop iterator bound limit width body).
Proof.
  refine {| private_rule_writes := [iterator];
    private_rule_source_writes := @frontend_memory_writes iterator bound body (@memory_body_writes_empty body BODY);
    private_rule_atoms := unit; private_rule_domain := stripmine_guard_domain iterator bound;
    private_rule_dimension := @stripmine_guard_dimension width iterator bound WIDTH;
    private_rule_primitives := @stripmine_guard_primitives width iterator bound WIDTH;
    private_rule_formula := Fact tt |}.
  - intros; eapply stripmine_source_domain; eauto.
  - intros temps p locals le memory le' final SCOPE RUN [ZERO [[n LOOKUP] RANGE]].
    cbn [entry_temps] in ZERO, LOOKUP, RANGE; unfold temp_word in RANGE; rewrite LOOKUP in RANGE.
    destruct (@stripmine_local (adapter_entry temps) (globalenv p) locals le memory le' final (Int.signed n)
      SCOPE ZERO ltac:(rewrite Int.repr_signed; exact LOOKUP) RANGE RUN) as [target [EXEC FRAME]].
    exists target,final; split; [exact EXEC|split; [exact FRAME|apply memory_equivalent_refl]].
Defined.
End RULE.
Print Assumptions stripmine_local.
Print Assumptions stripmine_region_rule.
