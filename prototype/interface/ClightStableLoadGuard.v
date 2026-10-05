From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr ClightNoWrap
  ClightSameAddress ClightDecisionRule ClightRedundantSet ClightPositiveCheck ClightMatrixGuard ClightCountedLoop
  ClightFramedLoop ClightCountedProtocol ClightZeroTrip ClightFrontendLoopProtocol ClightFrontendRegion
  ClightLoopExecution ClightLoopSyntax ClightStraightLine ClightTempFrame.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeSynthesis
  ClightReadonlyCellSwap ClightStableLoadBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition stable_loaded_word parameter entry := exists block offset value,
  (entry_temps entry) ! parameter = Some (Vptr block offset) /\
  Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) = Some value.
Definition stable_load_guard_domain iterator bound out parameter entry :=
  register_domain iterator entry /\ register_domain bound entry /\
  (register_equals iterator Int.zero tt entry ->
    expression_test (counter_condition iterator bound) entry true ->
    address_domain out parameter entry /\ stable_loaded_word parameter entry).
Definition stable_load_guard_property iterator bound out parameter (_ : unit) entry :=
  register_equals iterator Int.zero tt entry /\
  expression_test (counter_condition iterator bound) entry true /\ cell_pair_apart out parameter entry.
Definition stable_active_flag iterator bound (entry : clight_entry) :=
  (Int.signed (temp_word iterator (entry_temps entry)) <? Int.signed (temp_word bound (entry_temps entry))).
Definition stable_load_guard_accept iterator bound out parameter (_ : unit) entry :=
  register_flag iterator Int.zero entry && stable_active_flag iterator bound entry &&
    negb (address_accept out parameter entry).
Definition stable_load_guard_tree iterator bound out parameter :=
  Test (register_guard iterator Int.zero)
    (Test (counter_condition iterator bound)
      (Test (same_address_guard out parameter) (Decision false) (Decision true)) (Decision false))
    (Decision false).

Lemma stable_active_test iterator bound entry : iterator <> bound ->
  register_domain iterator entry -> register_domain bound entry ->
  expression_test (counter_condition iterator bound) entry (stable_active_flag iterator bound entry).
Proof.
  intros DISTINCT [x X] [upper UPPER].
  unfold stable_active_flag, temp_word; rewrite X, UPPER.
  apply (@counter_condition_at (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    iterator bound (Int.signed x) (Int.signed upper));
    try exact DISTINCT; try apply Int.signed_range; rewrite Int.repr_signed; assumption.
Qed.

Lemma stable_addresses_apart out parameter entry : address_domain out parameter entry ->
  negb (address_accept out parameter entry) = true -> cell_pair_apart out parameter entry.
Proof.
  intros [b1 [ofs1 [b2 [ofs2 [P [Q _]]]]]] ACCEPT SAME.
  assert (EQ : Vptr b1 ofs1 = Vptr b2 ofs2) by congruence; inversion EQ; subst.
  unfold address_accept, address_flag in ACCEPT; rewrite P, Q, Pos.eqb_refl, Ptrofs.eq_true in ACCEPT.
  discriminate.
Qed.

Lemma stable_load_guard_run iterator bound out parameter entry : iterator <> bound ->
  stable_load_guard_domain iterator bound out parameter entry ->
  decision_run entry (stable_load_guard_tree iterator bound out parameter)
    (stable_load_guard_accept iterator bound out parameter tt entry).
Proof.
  intros DISTINCT [I [N ADDRESSES]]; unfold stable_load_guard_tree, stable_load_guard_accept.
  eapply run_test; [apply register_expression_test; exact I|].
  destruct (register_flag iterator Int.zero entry) eqn:ZERO; cbn; [|constructor].
  eapply run_test; [apply stable_active_test; assumption|].
  destruct (stable_active_flag iterator bound entry) eqn:ACTIVE; cbn; [|constructor].
  assert (DOMAIN : address_domain out parameter entry).
  { apply (proj1 (ADDRESSES (register_flag_evidence Int.zero I ZERO)
      ltac:(pose proof (stable_active_test DISTINCT I N) as TEST; rewrite ACTIVE in TEST; exact TEST))). }
  eapply run_test; [apply (proj2 (@address_guard_correct out parameter entry _ DOMAIN)); reflexivity|].
  destruct (address_accept out parameter entry); constructor.
Qed.

Lemma stable_load_guard_sound iterator bound out parameter : iterator <> bound -> forall a entry,
  stable_load_guard_domain iterator bound out parameter entry ->
  stable_load_guard_accept iterator bound out parameter a entry = true ->
  stable_load_guard_property iterator bound out parameter a entry.
Proof.
  intros DISTINCT [] entry [I [N ADDRESSES]] ACCEPT; unfold stable_load_guard_accept in ACCEPT.
  apply andb_true_iff in ACCEPT as [PREFIX APART]; apply andb_true_iff in PREFIX as [ZERO ACTIVE].
  pose proof (register_flag_evidence Int.zero I ZERO) as ITER.
  pose proof (stable_active_test DISTINCT I N) as TEST; rewrite ACTIVE in TEST.
  split; [exact ITER|split; [exact TEST|]].
  apply stable_addresses_apart; [exact (proj1 (ADDRESSES ITER TEST))|exact APART].
Qed.

Definition stable_load_guard_primitives iterator bound out parameter (DISTINCT : iterator <> bound) :=
  @positive_tree_primitives unit (stable_load_guard_domain iterator bound out parameter)
    (stable_load_guard_property iterator bound out parameter) (stable_load_guard_accept iterator bound out parameter)
    (@stable_load_guard_sound iterator bound out parameter DISTINCT)
    (fun _ => stable_load_guard_tree iterator bound out parameter)
    (fun _ => ltac:(repeat constructor))
    (fun a entry DOMAIN => match a with tt => stable_load_guard_run DISTINCT DOMAIN end).

Definition stable_load_condition fe O (observe : fragment_observation -> O -> Prop)
  iterator bound out parameter (DISTINCT : iterator <> bound) :
  readonly_condition (readonly_clight_host fe observe)
    (stable_load_guard_domain iterator bound out parameter)
    (stable_load_guard_property iterator bound out parameter tt)
    (synthesize_decision_tree (stable_load_guard_primitives out parameter DISTINCT) (Fact tt)).
Proof.
  apply synthesized_scalar_tree_condition with
    (D := @positive_dimension clight_entry unit (stable_load_guard_domain iterator bound out parameter)
      (stable_load_guard_property iterator bound out parameter) (stable_load_guard_accept iterator bound out parameter)
      (@stable_load_guard_sound iterator bound out parameter DISTINCT)) (premise := Fact tt).
  - intros []; repeat constructor.
  - intros []; constructor.
Defined.

Theorem stable_load_domain_from_source fe ge locals le memory iterator bound out parameter body after final :
  flatten_region body = [stable_load_body out parameter iterator] ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
  stable_load_guard_domain iterator bound out parameter (Entry ge locals le memory).
Proof.
  intros FLAT SOURCE.
  destruct (@frontend_entry_test fe ge locals le memory iterator bound body after final SOURCE) as [flag TEST].
  destruct (@counter_test_domain iterator bound (Entry ge locals le memory) flag TEST) as [x [upper [I N]]].
  split; [exists x; exact I|split; [exists upper; exact N|]].
  intros ZERO ACTIVE.
  assert (WRITES : writes_only [] body).
  { apply flatten_writes_certificate; rewrite FLAT; constructor; [constructor|constructor]. }
  assert (NORMAL : normal_statement body = true).
  { apply flatten_normal_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. }
  assert (FRAME : forall before mem tr after mem',
    exec_stmt fe ge locals before mem body tr after mem' Out_normal -> temp_agree [iterator;bound] before after).
  { intros; eapply structured_temp_frame; [exact WRITES|intros id _ BAD; exact BAD|eassumption]. }
  destruct (frontend_iteration_decode ACTIVE (@normal_statement_execution fe ge locals body NORMAL) FRAME SOURCE)
    as [middle [mem [FIRST REST]]].
  apply (flattened_singleton_execution FLAT) in FIRST.
  destruct (stable_load_body_facts FIRST) as [b1 [ofs1 [b2 [ofs2 [value [stored [P [Q [LOAD STORE]]]]]]]]].
  split.
  - exists b1, ofs1, b2, ofs2; split; [exact P|split; [exact Q|split]].
    + apply writable_word_valid_pointer; exact (proj1 (@storev_word_facts _ _ _ _ _ STORE)).
    + eapply loaded_address_valid; exact LOAD.
  - exists b2, ofs2, value; auto.
Qed.

Print Assumptions stable_load_condition.
Print Assumptions stable_load_domain_from_source.
