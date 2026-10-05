From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightCountedProtocol ClightStraightLine
  ClightRegionProgress ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion CompCertStoreSchedule.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis
  ClightLoadedBoundSyntax ClightDualLoadedUnitGuard ClightReadonlyCellSwap ClightLoadedRectangleMemory ClightLoadedRectangleAtoms
  ClightDualRectanglePrefix ClightDualRectangleCursor.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition dual_rect_active parameter point entry := point < Int.signed (loaded_rectangle_word parameter entry).
Definition dual_rect_active_probe parameter point :=
  Test (loaded_rectangle_active_expr parameter point) (Decision true) (Decision false).

Lemma dual_rect_activity fe O (observe : fragment_observation -> O -> Prop) parameter point D :
  (forall entry, D entry -> signed_range point) -> (forall entry, D entry -> loaded_word_domain parameter entry) ->
  readonly_classifier (readonly_clight_host fe observe) D (dual_rect_active parameter point)
    (fun entry => ~ dual_rect_active parameter point entry) (dual_rect_active_probe parameter point).
Proof.
  intros RANGE DOMAIN; unfold dual_rect_active_probe; apply readonly_expression_classifier.
  - intros entry INV; destruct (DOMAIN entry INV) as [word [q [qo [Q READ]]]].
    exists (loaded_rectangle_active_flag parameter point entry); eapply loaded_rectangle_active_test; [exact (RANGE entry INV)|exact Q|exact READ].
  - intros entry INV TEST; destruct (DOMAIN entry INV) as [word [q [qo [Q READ]]]].
    assert (FLAG : loaded_rectangle_active_flag parameter point entry = true) by
      (eapply readonly_test_determinate; [eapply loaded_rectangle_active_test; [exact (RANGE entry INV)|exact Q|exact READ]|exact TEST]).
    apply Z.ltb_lt; exact FLAG.
  - intros entry INV TEST; destruct (DOMAIN entry INV) as [word [q [qo [Q READ]]]].
    assert (FLAG : loaded_rectangle_active_flag parameter point entry = false) by
      (eapply readonly_test_determinate; [eapply loaded_rectangle_active_test; [exact (RANGE entry INV)|exact Q|exact READ]|exact TEST]).
    apply Z.ltb_ge in FLAG; unfold dual_rect_active; lia.
Defined.

Definition dual_rect_point_probe d array rows columns i j :=
  Test (loaded_rectangle_alias_expr d array rows i j) (Decision false)
    (Test (loaded_rectangle_alias_expr d array columns i j) (Decision false) (Decision true)).
Definition dual_rect_point_property fe d array row rows columns outer i j entry :=
  loaded_rectangle_alias_flag d array rows i j entry = false /\
  loaded_rectangle_alias_flag d array columns i j entry = false /\
  (j+1 = Int.signed (loaded_rectangle_word columns entry) ->
    dual_rect_outer_invariant fe d row rows columns outer (i+1) entry).

Section INNER.
Variables d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables array row rows column columns : ident.
Variables body outer : statement.
Hypotheses (RC : row <> column) (RN : row <> rows) (RM : row <> columns)
  (CN : column <> rows) (CM : column <> columns).
Hypotheses (BODY : flatten_region body = [rect_store d array row column])
  (OUTER : flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body]).

Lemma dual_rect_point_ready i j entry :
  dual_rect_inner_invariant fe d row rows column columns body outer i j entry ->
  dual_rect_active columns j entry ->
  expression_test (loaded_rectangle_alias_expr d array rows i j) entry (loaded_rectangle_alias_flag d array rows i j entry) /\
  expression_test (loaded_rectangle_alias_expr d array columns i j) entry (loaded_rectangle_alias_flag d array columns i j entry).
Proof.
  intros [IR [JR [cursor]]] ACTIVE; set (state := dri_state cursor).
  destruct (@dual_rect_inner_step d VALID fe (entry_ge entry) (entry_env entry) (drs_temps state) (drs_memory state)
    array row column columns body i j (loaded_rectangle_word columns entry) (drs_r state) (drs_rofs state)
    (dri_exit cursor) (dri_exit_memory cursor) RC BODY ltac:(pose proof (drs_rows_range state); lia) (drs_columns_range state)
    ltac:(unfold dual_rect_active in ACTIVE; lia) (drs_iterator state) (dri_iterator cursor)
    (drs_columns state) (drs_columns_read state) (dri_inner cursor)) as [block [middle [ARRAY [STORE REST]]]].
  assert (INDEX : 0 <= i*rectangle_stride d+j < rectangle_extent d).
  { eapply rectangle_point_bound with (N := rectangle_outer_limit d) (M := Int.signed (loaded_rectangle_word columns entry)); [exact VALID| |apply (drs_columns_range state)| |].
    - pose proof (rectangle_limits VALID); lia.
    - pose proof (drs_rows_range state); lia.
    - unfold dual_rect_active in ACTIVE; lia. }
  assert (WORD : writable_word (entry_memory entry) block (loaded_rectangle_offset d i j)) by
    (apply (drs_permissions_back state); exact (@loaded_rectangle_store_word d VALID block i j _ _ INDEX STORE)).
  split.
  - eapply loaded_rectangle_alias_test; [exact VALID|exact INDEX|exact ARRAY|apply (drs_entry_rows state)|
      apply (drs_entry_rows_read state)|exact WORD].
  - eapply loaded_rectangle_alias_test; [exact VALID|exact INDEX|exact ARRAY|apply (drs_entry_columns state)|
      apply (drs_entry_columns_read state)|exact WORD].
Qed.

Lemma dual_rect_point_next i j entry :
  dual_rect_inner_invariant fe d row rows column columns body outer i j entry ->
  dual_rect_active columns j entry ->
  loaded_rectangle_alias_flag d array rows i j entry = false ->
  loaded_rectangle_alias_flag d array columns i j entry = false ->
  dual_rect_point_property fe d array row rows columns outer i j entry /\
  dual_rect_inner_invariant fe d row rows column columns body outer i (j+1) entry.
Proof.
  intros [IR [JR [cursor]]] ACTIVE AQ AM; set (state := dri_state cursor).
  destruct (@dual_rect_inner_step d VALID fe (entry_ge entry) (entry_env entry) (drs_temps state) (drs_memory state)
    array row column columns body i j (loaded_rectangle_word columns entry) (drs_r state) (drs_rofs state)
    (dri_exit cursor) (dri_exit_memory cursor) RC BODY ltac:(pose proof (drs_rows_range state); lia) (drs_columns_range state)
    ltac:(unfold dual_rect_active in ACTIVE; lia) (drs_iterator state) (dri_iterator cursor)
    (drs_columns state) (drs_columns_read state) (dri_inner cursor)) as [block [middle [ARRAY [STORE INNER]]]].
  assert (INDEX : 0 <= i*rectangle_stride d+j < rectangle_extent d).
  { eapply rectangle_point_bound with (N := rectangle_outer_limit d) (M := Int.signed (loaded_rectangle_word columns entry)); [exact VALID| |apply (drs_columns_range state)| |].
    - pose proof (rectangle_limits VALID); lia.
    - pose proof (drs_rows_range state); lia.
    - unfold dual_rect_active in ACTIVE; lia. }
  set (next_state := @dual_rect_state_store d VALID row rows column columns i j entry state block middle RC CN CM INDEX STORE
    (@loaded_rectangle_alias_apart d array rows i j entry block (drs_q state) (drs_qofs state) ARRAY (drs_entry_rows state) AQ)
    (@loaded_rectangle_alias_apart d array columns i j entry block (drs_r state) (drs_rofs state) ARRAY (drs_entry_columns state) AM)).
  assert (NEXT_INNER : dual_rect_inner_invariant fe d row rows column columns body outer i (j+1) entry).
  { split; [exact IR|split; [pose proof (drs_columns_range state); unfold dual_rect_active in ACTIVE; lia|constructor]].
    refine {| dri_state := next_state; dri_iterator := PTree.gss _ _ _;
      dri_exit := dri_exit cursor; dri_exit_memory := dri_exit_memory cursor;
      dri_next := dri_next cursor; dri_next_memory := dri_next_memory cursor;
      dri_after := dri_after cursor; dri_final := dri_final cursor;
      dri_inner := INNER; dri_increment := dri_increment cursor; dri_tail := dri_tail cursor |}. }
  split; [|exact NEXT_INNER]; unfold dual_rect_point_property; split; [exact AQ|split; [exact AM|]].
  intro LAST.
  assert (COL : (drs_temps next_state) ! column = Some (Vint (loaded_rectangle_word columns entry))).
  { change ((PTree.set column (Vint (Int.repr (j+1))) (drs_temps state)) ! column =
      Some (Vint (loaded_rectangle_word columns entry))).
    rewrite PTree.gss, LAST, Int.repr_signed; reflexivity. }
  pose proof (@dual_rect_close_row fe (entry_ge entry) (entry_env entry) (drs_temps next_state) (drs_memory next_state)
    row rows column columns body outer i (loaded_rectangle_word rows entry) (loaded_rectangle_word columns entry)
    (drs_r next_state) (drs_rofs next_state) (dri_exit cursor) (dri_exit_memory cursor)
    (dri_next cursor) (dri_next_memory cursor) (dri_after cursor) (dri_final cursor)
    IR
    (drs_iterator next_state) COL (drs_columns next_state) (drs_columns_read next_state)
    (@rect_body_quiet d array row column body BODY) INNER (dri_increment cursor) (dri_tail cursor)) as TAIL.
  split; [pose proof (drs_rows_range state); lia|constructor].
  refine {| dro_state := @dual_rect_state_increment d row rows columns i entry next_state RN RM;
    dro_after := dri_after cursor; dro_final := dri_final cursor; dro_tail := TAIL |}.
Qed.

Definition dual_rect_inner_point O (observe : fragment_observation -> O -> Prop) i j :
  readonly_condition (readonly_clight_host fe observe)
    (fun entry => dual_rect_inner_invariant fe d row rows column columns body outer i j entry /\ dual_rect_active columns j entry)
    (fun entry => dual_rect_point_property fe d array row rows columns outer i j entry /\
      dual_rect_inner_invariant fe d row rows column columns body outer i (j+1) entry)
    (dual_rect_point_probe d array rows columns i j).
Proof.
  constructor.
  - intros entry [INV ACTIVE]; destruct (dual_rect_point_ready INV ACTIVE) as [Q R].
    cbn [dual_rect_point_probe readonly_tree_safe]; split; [eauto|].
    intros answer RUN; destruct answer; [exact I|split; [eauto|intros second SECOND; destruct second; exact I]].
  - intros entry [INV ACTIVE]; destruct (dual_rect_point_ready INV ACTIVE) as [Q R].
    exists (negb (loaded_rectangle_alias_flag d array rows i j entry) &&
      negb (loaded_rectangle_alias_flag d array columns i j entry)), entry; split; [|reflexivity].
    unfold dual_rect_point_probe; eapply run_test; [exact Q|].
    destruct (loaded_rectangle_alias_flag d array rows i j entry); cbn; [constructor|].
    eapply run_test; [exact R|]; destruct (loaded_rectangle_alias_flag d array columns i j entry); constructor.
  - intros entry answer checked [INV ACTIVE] [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    destruct (dual_rect_point_ready INV ACTIVE) as [Q R].
    assert (ALIASES : loaded_rectangle_alias_flag d array rows i j entry = false /\
      loaded_rectangle_alias_flag d array columns i j entry = false).
    { unfold dual_rect_point_probe in RUN; inversion RUN; subst.
      match goal with LEAF : decision_run _ (if ?choice then Decision false else _) true |- _ =>
        destruct choice; [inversion LEAF|] end.
      match goal with TREE : decision_run _ (Test _ _ _) true |- _ => inversion TREE; subst end.
      match goal with LEAF : decision_run _ (if ?choice then Decision false else Decision true) true |- _ =>
        destruct choice; inversion LEAF; subst end.
      split; eapply readonly_test_determinate; eassumption. }
    destruct ALIASES as [AQ AM]; exact (dual_rect_point_next INV ACTIVE AQ AM).
Defined.

Definition dual_rect_inner_spec O (observe : fragment_observation -> O -> Prop) (i : Z) : readonly_prefix_spec (readonly_clight_host fe observe) Z.
Proof.
  refine (@ReadonlyPrefixSpec clight_entry (readonly_clight_host fe observe) Z (fun j => j+1)
    (dual_rect_active_probe columns) (dual_rect_point_probe d array rows columns i)
    (dual_rect_inner_invariant fe d row rows column columns body outer i) (dual_rect_active columns)
    (dual_rect_point_property fe d array row rows columns outer i) _ (dual_rect_inner_point observe i)).
  intro j; apply dual_rect_activity.
  - intros entry [IR [JR REST]]; pose proof (rectangle_limits VALID); unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia.
  - intros entry [IR [JR [cursor]]]; exists (loaded_rectangle_word columns entry),
      (drs_r (dri_state cursor)), (drs_rofs (dri_state cursor)); split; apply drs_entry_columns || apply drs_entry_columns_read.
Defined.
End INNER.
