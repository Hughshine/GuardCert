From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightPureExpr ClightNoWrap ClightRedundantSet ClightMatrixGuard
  ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol ClightLoopSyntax ClightLoopExecution
  ClightStraightLine ClightRegionProgress ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis ClightQuietDeterminacy ClightLoopBridge
  ClightLoadedBoundSyntax ClightLoadedBoundGuard ClightLoadedMatrixSyntax ClightStrictLoopProgress ClightLoadedRectangleRow ClightLoadedRectangleAtoms
  ClightLoadedRectangleInnerScan ClightLoadedRectanglePrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_rectangle_domain row bound outer_body entry :=
  loaded_bound_entry row bound entry /\ quiet_source_completion (loaded_rectangle_source row bound outer_body) entry.
Definition loaded_rectangle_setup d row bound columns :=
  Test (register_guard row Int.zero)
    (Test (loaded_rectangle_active_expr bound 0)
      (Test (loaded_rectangle_limit_expr bound (rectangle_outer_limit d))
        (register_range_tree columns (rectangle_stride d)) (Decision false)) (Decision false)) (Decision false).
Definition loaded_rectangle_setup_accept d row bound columns entry :=
  register_flag row Int.zero entry && loaded_rectangle_active_flag bound 0 entry &&
    loaded_rectangle_limit_flag bound (rectangle_outer_limit d) entry && register_range_flag columns (rectangle_stride d) entry.
Definition loaded_rectangle_setup_property d row bound columns entry :=
  register_equals row Int.zero tt entry /\
  0 < Int.signed (loaded_rectangle_word bound entry) <= rectangle_outer_limit d /\ register_range columns (rectangle_stride d) entry.

Lemma loaded_rectangle_domain_run d array row bound column columns body outer_body entry :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_rectangle_domain row bound outer_body entry ->
  exists after final, forall fe, exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (loaded_rectangle_source row bound outer_body) E0 after final Out_normal.
Proof.
  intros BODY OUTER [ENTRY [observed COMPLETE]].
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  pose proof (COMPLETE (adapter_entry true)) as SOURCE.
  pose proof (@loaded_rectangle_source_quiet d array row bound column columns body outer_body BODY OUTER) as QUIET.
  pose proof (@quiet_execution_silent _ ge locals le memory _ trace after final outcome SOURCE QUIET) as SILENT.
  pose proof (@quiet_loop_normal _ ge locals le memory _ _ trace after final outcome QUIET SOURCE) as NORMAL.
  subst trace outcome; exists after, final; exact COMPLETE.
Qed.

Lemma loaded_rectangle_active_columns d array row bound column columns body outer_body entry :
  column <> columns -> flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_rectangle_domain row bound outer_body entry -> register_flag row Int.zero entry = true ->
  loaded_rectangle_active_flag bound 0 entry = true -> register_domain columns entry.
Proof.
  intros CM BODY OUTER DOMAIN ZERO ACTIVE.
  destruct DOMAIN as [[word [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE].
  assert (ROW : (entry_temps entry) ! row = Some (Vint Int.zero)) by
    (apply register_flag_evidence; [exists word; exact ITER|exact ZERO]).
  unfold loaded_rectangle_active_flag, loaded_rectangle_word in ACTIVE; rewrite BOUND, READ in ACTIVE; apply Z.ltb_lt in ACTIVE.
  assert (LT : Int.lt Int.zero upper = true).
  { unfold Int.lt; change (Int.signed Int.zero) with 0; destruct (zlt 0 (Int.signed upper)); [reflexivity|lia]. }
  assert (HEAD : expression_test (loaded_bound_test row bound) entry true).
  { rewrite <- LT; destruct entry; eapply loaded_bound_test_eval; eassumption. }
  destruct (@loaded_rectangle_domain_run d array row bound column columns body outer_body entry BODY OUTER
    ltac:(split; [do 4 eexists; repeat split; eassumption|exact COMPLETE])) as [after [final SOURCE]].
  destruct entry; exact (@loaded_rectangle_columns_domain (adapter_entry true) _ _ _ _ d array row bound column columns body outer_body
    after final CM BODY OUTER HEAD (SOURCE (adapter_entry true))).
Qed.

Lemma loaded_rectangle_setup_run d (VALID : rectangle_layout_valid d) array row bound column columns body outer_body entry :
  column <> columns -> flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_rectangle_domain row bound outer_body entry ->
  decision_run entry (loaded_rectangle_setup d row bound columns) (loaded_rectangle_setup_accept d row bound columns entry).
Proof.
  intros CM BODY OUTER DOMAIN.
  destruct DOMAIN as [[word [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE].
  assert (DOMAIN : loaded_rectangle_domain row bound outer_body entry) by
    (split; [do 4 eexists; repeat split; eassumption|exact COMPLETE]).
  unfold loaded_rectangle_setup, loaded_rectangle_setup_accept.
  eapply run_test; [apply register_expression_test; exists word; exact ITER|].
  destruct (register_flag row Int.zero entry) eqn:ZERO; cbn; [|constructor].
  eapply run_test; [eapply loaded_rectangle_active_test;
    [change (-2147483648 <= 0 <= 2147483647); lia|exact BOUND|exact READ]|].
  destruct (loaded_rectangle_active_flag bound 0 entry) eqn:ACTIVE; cbn; [|constructor].
  eapply run_test; [eapply loaded_rectangle_limit_test;
    [pose proof (rectangle_limits VALID); tauto|exact BOUND|exact READ]|].
  destruct (loaded_rectangle_limit_flag bound (rectangle_outer_limit d) entry); cbn; [|constructor].
  apply register_range_tree_run.
  exact (@loaded_rectangle_active_columns d array row bound column columns body outer_body entry CM BODY OUTER DOMAIN ZERO ACTIVE).
Qed.

Lemma loaded_rectangle_setup_sound d (VALID : rectangle_layout_valid d) array row bound column columns body outer_body entry :
  column <> columns -> flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_rectangle_domain row bound outer_body entry -> loaded_rectangle_setup_accept d row bound columns entry = true ->
  loaded_rectangle_setup_property d row bound columns entry.
Proof.
  intros CM BODY OUTER DOMAIN ACCEPT.
  unfold loaded_rectangle_setup_accept in ACCEPT; repeat rewrite andb_true_iff in ACCEPT.
  destruct ACCEPT as [[[ZERO ACTIVE] LIMIT] COLS].
  assert (M_DOMAIN : register_domain columns entry) by
    (exact (@loaded_rectangle_active_columns d array row bound column columns body outer_body entry CM BODY OUTER DOMAIN ZERO ACTIVE)).
  destruct DOMAIN as [[word [upper [q [qofs [ITER REST]]]]] COMPLETE].
  split; [apply register_flag_evidence; [exists word; exact ITER|exact ZERO]|split].
  - unfold loaded_rectangle_active_flag in ACTIVE; apply Z.ltb_lt in ACTIVE.
    unfold loaded_rectangle_limit_flag in LIMIT; apply Z.leb_le in LIMIT; lia.
  - apply register_range_sound; [pose proof (rectangle_limits VALID); tauto|exact M_DOMAIN|exact COLS].
Qed.

Definition loaded_rectangle_setup_condition d (VALID : rectangle_layout_valid d) fe O
  (observe : fragment_observation -> O -> Prop) (array row bound column columns : ident) (body outer_body : statement)
  (CM : column <> columns) (BODY : flatten_region body = [rect_store d array row column])
  (OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body]) :
  readonly_condition (readonly_clight_host fe observe) (loaded_rectangle_domain row bound outer_body)
    (loaded_rectangle_setup_property d row bound columns) (loaded_rectangle_setup d row bound columns).
Proof.
  constructor.
  - intros entry DOMAIN; apply readonly_decision_run_safe with (answer := loaded_rectangle_setup_accept d row bound columns entry).
    exact (@loaded_rectangle_setup_run d VALID array row bound column columns body outer_body entry CM BODY OUTER DOMAIN).
  - intros entry DOMAIN; exists (loaded_rectangle_setup_accept d row bound columns entry), entry; split; [|reflexivity].
    exact (@loaded_rectangle_setup_run d VALID array row bound column columns body outer_body entry CM BODY OUTER DOMAIN).
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    apply (@loaded_rectangle_setup_sound d VALID array row bound column columns body outer_body entry CM BODY OUTER DOMAIN).
    eapply readonly_decision_determinate; [exact (@loaded_rectangle_setup_run d VALID array row bound column columns body outer_body entry CM BODY OUTER DOMAIN)|exact RUN].
Defined.

Lemma loaded_rectangle_initial_prefix d (VALID : rectangle_layout_valid d) fe array row bound column columns body outer_body entry :
  row <> bound -> row <> column -> bound <> column -> row <> columns -> column <> columns ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_rectangle_domain row bound outer_body entry -> loaded_rectangle_setup_property d row bound columns entry ->
  loaded_rectangle_prefix_invariant fe d array row bound column columns body outer_body 0 entry.
Proof.
  intros RQ RC QC RM CM BODY OUTER DOMAIN [ZERO [NR [[m COLS] MR]]].
  destruct (@loaded_rectangle_domain_run d array row bound column columns body outer_body entry BODY OUTER DOMAIN)
    as [after [final SOURCE]].
  destruct DOMAIN as [[word [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE].
  unfold loaded_rectangle_word in NR; rewrite BOUND, READ in NR.
  unfold temp_word in MR; rewrite COLS in MR.
  assert (COLS' : (entry_temps entry) ! columns = Some (Vint (Int.repr (Int.signed m))))
    by (rewrite Int.repr_signed; exact COLS).
  destruct (@loaded_rectangle_row_step d VALID fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    array row bound column columns body outer_body after final 0 upper (Int.signed m) q qofs
    RQ RC QC RM CM BODY OUTER NR MR ltac:(lia) ZERO BOUND READ COLS' (SOURCE fe)) as [row_memory [POINTS TAIL]].
  assert (ARRAY : exists block, rect_array_binding d (entry_ge entry) (entry_env entry) array block).
  { destruct (Z.to_nat (Int.signed m)) eqn:COUNT.
    - pose proof (Z2Nat.id (Int.signed m) ltac:(lia)); rewrite COUNT in H; cbn in H; lia.
    - inversion POINTS; subst; match goal with FIRST : rect_point _ _ _ _ _ _ _ _ |- _ =>
        destruct FIRST as [block [ARRAY STORE]]; exists block; exact ARRAY end. }
  destruct ARRAY as [block ARRAY].
  split; [pose proof (rectangle_limits VALID); lia|].
  exists upper, (Int.signed m), block, q, qofs, (entry_temps entry), (entry_memory entry), after, final.
  split; [exact NR|split; [exact MR|split; [exact COLS'|split; [exact ARRAY|split; [exact BOUND|split; [exact READ|]]]]]].
  split; [exact ZERO|split; [exact COLS'|split; [exact BOUND|split; [exact READ|split; [intros; assumption|exact (SOURCE fe)]]]]].
Qed.

Lemma loaded_rectangle_scan_sound d VALID fe O (observe : fragment_observation -> O -> Prop)
  array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER fuel point entry :
  prefix_scan_property (@loaded_rectangle_prefix_spec d VALID fe O observe array row bound column columns body outer_body
    RQ RC QC RM CM BODY OUTER) fuel point entry ->
  forall i, point <= i < point+Z.of_nat fuel -> i < Int.signed (loaded_rectangle_word bound entry) ->
    loaded_rectangle_row_property d array bound columns i entry.
Proof.
  revert point; induction fuel as [|fuel IH]; intros point PROP i RANGE ACTIVE;
    cbn [prefix_scan_property loaded_rectangle_prefix_spec prefix_active prefix_next prefix_point_property] in PROP;
    [cbn in RANGE; lia|].
  destruct (PROP ltac:(unfold loaded_rectangle_prefix_active; lia)) as [ROW NEXT].
  destruct (Z.eq_dec i point); [subst; exact ROW|].
  eapply IH; [exact NEXT|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.

Definition loaded_rectangle_property d array row bound columns entry :=
  loaded_rectangle_setup_property d row bound columns entry /\
  forall i, 0 <= i < Int.signed (loaded_rectangle_word bound entry) -> loaded_rectangle_row_property d array bound columns i entry.

Definition loaded_rectangle_tree d VALID fe O (observe : fragment_observation -> O -> Prop)
  array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER :=
  decision_bind (loaded_rectangle_setup d row bound columns)
    (synthesize_prefix_scan (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
      (@loaded_rectangle_prefix_spec d VALID fe O observe array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER)
      (Z.to_nat (rectangle_outer_limit d)) 0) (Decision false).

Definition loaded_rectangle_condition d (VALID : rectangle_layout_valid d) fe O
  (observe : fragment_observation -> O -> Prop) array row bound column columns body outer_body
  RQ RC QC RM CM BODY OUTER :
  readonly_condition (readonly_clight_host fe observe) (loaded_rectangle_domain row bound outer_body)
    (loaded_rectangle_property d array row bound columns)
    (@loaded_rectangle_tree d VALID fe O observe array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER).
Proof.
  eapply readonly_condition_entails.
  - eapply sequence_readonly_conditions with (A := clight_readonly_check_algebra fe observe).
    + exact (@loaded_rectangle_setup_condition d VALID fe O observe array row bound column columns body outer_body CM BODY OUTER).
    + eapply readonly_condition_restrict.
      * exact (@synthesized_prefix_scan_condition clight_entry (readonly_clight_host fe observe) Z
          (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
          (@loaded_rectangle_prefix_spec d VALID fe O observe array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER)
          (Z.to_nat (rectangle_outer_limit d)) 0).
      * intros entry [DOMAIN SETUP]; exact (@loaded_rectangle_initial_prefix d VALID fe array row bound column columns body outer_body
          entry RQ RC QC RM CM BODY OUTER DOMAIN SETUP).
  - intros entry DOMAIN [SETUP SCAN]; split; [exact SETUP|].
    intros i IR; eapply loaded_rectangle_scan_sound; [exact SCAN| |lia].
    destruct SETUP as [ZERO [NR MR]]; cbn; rewrite Z2Nat.id by (pose proof (rectangle_limits VALID); lia); lia.
Defined.

Definition loaded_rectangle_generated_tree d VALID array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER :=
  @loaded_rectangle_tree d VALID (adapter_entry true) fragment_observation eq
    array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER.

Lemma loaded_rectangle_prefix_syntax d VALID fe O (observe : fragment_observation -> O -> Prop)
  array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER fuel point :
  synthesize_prefix_scan (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
    (@loaded_rectangle_prefix_spec d VALID fe O observe array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER) fuel point =
  synthesize_prefix_scan (clight_readonly_check_algebra (adapter_entry true) eq)
    (clight_readonly_branch_algebra (adapter_entry true) eq)
    (@loaded_rectangle_prefix_spec d VALID (adapter_entry true) fragment_observation eq
      array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER) fuel point.
Proof.
  revert point; induction fuel as [|fuel IH]; intro point; cbn [synthesize_prefix_scan
    loaded_rectangle_prefix_spec prefix_next prefix_active_probe prefix_point_probe
    clight_readonly_check_algebra clight_readonly_branch_algebra constant_check branch_check].
  - reflexivity.
  - rewrite IH; unfold loaded_rectangle_inner_tree.
    rewrite (@loaded_rectangle_inner_syntax d VALID fe O observe array bound columns point (Z.to_nat (rectangle_stride d)) 0).
    reflexivity.
Qed.

Definition loaded_rectangle_generated_condition d (VALID : rectangle_layout_valid d) fe O
  (observe : fragment_observation -> O -> Prop) array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER :
  readonly_condition (readonly_clight_host fe observe) (loaded_rectangle_domain row bound outer_body)
    (loaded_rectangle_property d array row bound columns)
    (@loaded_rectangle_generated_tree d VALID array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER).
Proof.
  unfold loaded_rectangle_generated_tree, loaded_rectangle_tree.
  rewrite <- (@loaded_rectangle_prefix_syntax d VALID fe O observe array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER).
  exact (@loaded_rectangle_condition d VALID fe O observe array row bound column columns body outer_body RQ RC QC RM CM BODY OUTER).
Defined.

Lemma loaded_rectangle_domain_from_source d fe ge locals le memory array row bound column columns body outer_body after final :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  exec_stmt fe ge locals le memory (loaded_rectangle_source row bound outer_body) E0 after final Out_normal ->
  loaded_rectangle_domain row bound outer_body (Entry ge locals le memory).
Proof.
  intros BODY OUTER SOURCE; split.
  - assert (HEAD : exists flag, expression_test (loaded_bound_test row bound) (Entry ge locals le memory) flag).
    { exact (@loaded_matrix_entry_test fe ge locals le memory row bound outer_body after final SOURCE). }
    destruct HEAD as [flag TEST]; destruct (loaded_bound_test_facts TEST) as [word [upper [q [qofs [ITER [BOUND [READ FLAG]]]]]]].
    exists word, upper, q, qofs; repeat split; assumption.
  - eapply quiet_source_completion_from_run with (observed := FragmentObservation E0 after final Out_normal);
      [exact (@loaded_rectangle_source_quiet d array row bound column columns body outer_body BODY OUTER)|exact SOURCE].
Qed.

Print Assumptions loaded_rectangle_setup_condition.
Print Assumptions loaded_rectangle_initial_prefix.
Print Assumptions loaded_rectangle_scan_sound.
Print Assumptions loaded_rectangle_condition.
Print Assumptions loaded_rectangle_generated_condition.
Print Assumptions loaded_rectangle_prefix_syntax.
Print Assumptions loaded_rectangle_domain_from_source.
