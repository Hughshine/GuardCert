From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightRedundantSet ClightMatrixGuard ClightCountedLoop
  ClightStraightLine ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightReadonlyLoadedTreeSynthesis
  ClightLoadedBoundSyntax ClightLoadedBoundGuard ClightStableLoopCondition ClightQuietDeterminacy ClightDualLoadedUnitSyntax ClightDualLoadedUnitGuard
  ClightLoadedRectangleAtoms ClightDualRectanglePrefix ClightDualRectangleCursor ClightDualRectangleInnerScan ClightDualRectangleOuterScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition dual_rect_domain row rows outer entry := exists after final, forall fe,
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (dual_rect_source row rows outer) E0 after final Out_normal.
Lemma dual_rect_domain_entry row rows outer entry : dual_rect_domain row rows outer entry ->
  register_domain row entry /\ loaded_word_domain rows entry.
Proof.
  destruct entry as [ge locals le memory]; intros [after [final SOURCE]].
  destruct (@loaded_source_head (fun _ _ _ _ _ _ _ => False) ge locals row rows outer le memory after final (SOURCE _)) as [flag TEST].
  destruct (loaded_bound_test_facts TEST) as [i [upper [q [qo [I [Q [READ _]]]]]]]; split; [exists i; exact I|exists upper,q,qo; auto].
Qed.
Lemma dual_rect_word_known parameter entry word q qo :
  (entry_temps entry) ! parameter = Some (Vptr q qo) -> Mem.loadv Mint32 (entry_memory entry) (Vptr q qo) = Some (Vint word) ->
  loaded_rectangle_word parameter entry = word.
Proof. intros Q READ; unfold loaded_rectangle_word; rewrite Q, READ; reflexivity. Qed.

Definition dual_rect_setup d row rows columns := Test (register_guard row Int.zero)
  (Test (loaded_rectangle_active_expr rows 0)
    (Test (loaded_rectangle_limit_expr rows (rectangle_outer_limit d))
      (Test (loaded_rectangle_active_expr columns 0)
        (Test (loaded_rectangle_limit_expr columns (rectangle_stride d)) (Decision true) (Decision false))
        (Decision false)) (Decision false)) (Decision false)) (Decision false).
Definition dual_rect_setup_accept d row rows columns entry := register_flag row Int.zero entry &&
  (loaded_rectangle_active_flag rows 0 entry && (loaded_rectangle_limit_flag rows (rectangle_outer_limit d) entry &&
    (loaded_rectangle_active_flag columns 0 entry && loaded_rectangle_limit_flag columns (rectangle_stride d) entry))).
Definition dual_rect_setup_property d row rows columns entry := register_equals row Int.zero tt entry /\
  0 < Int.signed (loaded_rectangle_word rows entry) <= rectangle_outer_limit d /\
  0 < Int.signed (loaded_rectangle_word columns entry) <= rectangle_stride d /\ loaded_word_domain columns entry.

Section SETUP.
Variables d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variables array row rows column columns : ident.
Variables body outer : statement.
Hypothesis CM : column <> columns.
Hypotheses (BODY : flatten_region body = [rect_store d array row column])
  (OUTER : flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body]).

Lemma dual_rect_columns_defined entry : dual_rect_domain row rows outer entry ->
  register_flag row Int.zero entry = true -> loaded_rectangle_active_flag rows 0 entry = true -> loaded_word_domain columns entry.
Proof.
  intros DOMAIN ZERO ACTIVE; destruct DOMAIN as [after [final SOURCE]].
  destruct (proj1 (dual_rect_domain_entry ltac:(exists after,final; exact SOURCE))) as [i I].
  destruct (proj2 (dual_rect_domain_entry ltac:(exists after,final; exact SOURCE))) as [upper [q [qo [Q READ]]]].
  assert (ROW : (entry_temps entry) ! row = Some (Vint Int.zero)) by (eapply register_flag_evidence; [exists i; exact I|exact ZERO]).
  unfold loaded_rectangle_active_flag in ACTIVE; rewrite (@dual_rect_word_known rows entry upper q qo Q READ) in ACTIVE; apply Z.ltb_lt in ACTIVE.
  destruct (@dual_rect_open_row (fun _ _ _ _ _ _ _ => False) (entry_ge entry) (entry_env entry) (entry_temps entry)
    (entry_memory entry) d array row rows column columns body outer 0 upper q qo after final BODY OUTER ltac:(lia)
    ROW Q READ (SOURCE _)) as [exit [exit_memory [next [next_memory [INNER REST]]]]].
  destruct (loaded_source_head INNER) as [flag TEST].
  destruct (loaded_bound_test_facts TEST) as [j [width [r [ro [J [R [READ2 _]]]]]]].
  rewrite PTree.gso in R by congruence; exists width,r,ro; auto.
Qed.

Lemma dual_rect_setup_run entry : dual_rect_domain row rows outer entry ->
  decision_run entry (dual_rect_setup d row rows columns) (dual_rect_setup_accept d row rows columns entry).
Proof.
  intro DOMAIN; destruct (dual_rect_domain_entry DOMAIN) as [[i I] [upper [q [qo [Q READ]]]]].
  unfold dual_rect_setup,dual_rect_setup_accept; eapply run_test; [apply register_expression_test; exists i; exact I|].
  destruct (register_flag row Int.zero entry) eqn:ZERO; cbn; [|constructor].
  eapply run_test; [eapply loaded_rectangle_active_test; [change (-2147483648 <= 0 <= 2147483647); lia|exact Q|exact READ]|].
  destruct (loaded_rectangle_active_flag rows 0 entry) eqn:ACTIVE; cbn; [|constructor].
  eapply run_test; [eapply loaded_rectangle_limit_test; [pose proof (rectangle_limits VALID); tauto|exact Q|exact READ]|].
  destruct (loaded_rectangle_limit_flag rows (rectangle_outer_limit d) entry); cbn; [|constructor].
  destruct (dual_rect_columns_defined DOMAIN ZERO ACTIVE) as [width [r [ro [R READ2]]]].
  eapply run_test; [eapply loaded_rectangle_active_test; [change (-2147483648 <= 0 <= 2147483647); lia|exact R|exact READ2]|].
  destruct (loaded_rectangle_active_flag columns 0 entry); cbn; [|constructor].
  eapply run_test; [eapply loaded_rectangle_limit_test; [pose proof (rectangle_limits VALID); tauto|exact R|exact READ2]|].
  destruct (loaded_rectangle_limit_flag columns (rectangle_stride d) entry); constructor.
Qed.
Lemma dual_rect_setup_sound entry : dual_rect_domain row rows outer entry ->
  dual_rect_setup_accept d row rows columns entry = true -> dual_rect_setup_property d row rows columns entry.
Proof.
  intros DOMAIN ACCEPT; unfold dual_rect_setup_accept in ACCEPT; rewrite !andb_true_iff in ACCEPT.
  destruct ACCEPT as [ZERO [N [NL [M ML]]]].
  assert (COLS : loaded_word_domain columns entry) by (apply dual_rect_columns_defined; assumption).
  unfold loaded_rectangle_active_flag in N,M; unfold loaded_rectangle_limit_flag in NL,ML;
    apply Z.ltb_lt in N,M; apply Z.leb_le in NL,ML.
  repeat split; try assumption.
  apply register_flag_evidence; [exact (proj1 (dual_rect_domain_entry DOMAIN))|exact ZERO].
Qed.
Definition dual_rect_setup_condition fe O (observe : fragment_observation -> O -> Prop) :
  readonly_condition (readonly_clight_host fe observe) (dual_rect_domain row rows outer)
    (dual_rect_setup_property d row rows columns) (dual_rect_setup d row rows columns).
Proof.
  constructor.
  - intros entry DOMAIN; apply readonly_decision_run_safe with (answer := dual_rect_setup_accept d row rows columns entry); apply dual_rect_setup_run; assumption.
  - intros entry DOMAIN; exists (dual_rect_setup_accept d row rows columns entry),entry; split; [apply dual_rect_setup_run; assumption|reflexivity].
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    apply dual_rect_setup_sound; [exact DOMAIN|].
    eapply readonly_decision_determinate; [apply dual_rect_setup_run; exact DOMAIN|exact RUN].
Defined.

Lemma dual_rect_initial_cursor fe entry : dual_rect_domain row rows outer entry ->
  dual_rect_setup_property d row rows columns entry -> dual_rect_outer_invariant fe d row rows columns outer 0 entry.
Proof.
  intros DOMAIN [ZERO [NR [MR [width [r [ro [R READ2]]]]]]].
  destruct (proj2 (dual_rect_domain_entry DOMAIN)) as [upper [q [qo [Q READ]]]].
  destruct DOMAIN as [after [final SOURCE]].
  assert (READ_N : Mem.loadv Mint32 (entry_memory entry) (Vptr q qo) = Some (Vint (loaded_rectangle_word rows entry))) by
    (rewrite (@dual_rect_word_known rows entry upper q qo Q READ); exact READ).
  assert (READ_M : Mem.loadv Mint32 (entry_memory entry) (Vptr r ro) = Some (Vint (loaded_rectangle_word columns entry))) by
    (rewrite (@dual_rect_word_known columns entry width r ro R READ2); exact READ2).
  split; [pose proof (rectangle_limits VALID); lia|constructor].
  refine {| dro_state := {| drs_rows_range := NR; drs_columns_range := MR;
    drs_q := q; drs_qofs := qo; drs_r := r; drs_rofs := ro; drs_entry_rows := Q; drs_entry_columns := R;
    drs_entry_rows_read := READ_N; drs_entry_columns_read := READ_M;
    drs_temps := entry_temps entry; drs_memory := entry_memory entry;
    drs_iterator := ZERO; drs_rows := Q; drs_columns := R; drs_rows_read := READ_N; drs_columns_read := READ_M;
    drs_permissions_back := fun b ofs WORD => WORD |}; dro_after := after; dro_final := final; dro_tail := SOURCE fe |}.
Qed.
End SETUP.

Definition dual_rect_property d array row rows columns entry := dual_rect_setup_property d row rows columns entry /\
  forall i j, 0 <= i < Int.signed (loaded_rectangle_word rows entry) -> 0 <= j < Int.signed (loaded_rectangle_word columns entry) ->
    loaded_rectangle_alias_flag d array rows i j entry = false /\ loaded_rectangle_alias_flag d array columns i j entry = false.

Definition dual_rect_tree d VALID fe O (observe : fragment_observation -> O -> Prop) array row rows column columns body outer RC RN RM CN CM BODY OUTER :=
  decision_bind (dual_rect_setup d row rows columns)
    (@dual_rect_outer_tree d VALID fe array row rows column columns body outer RC RN RM CN CM BODY OUTER O observe) (Decision false).
Definition dual_rect_condition d (VALID : rectangle_layout_valid d) fe O (observe : fragment_observation -> O -> Prop)
  array row rows column columns body outer RC RN RM CN CM BODY OUTER :
  readonly_condition (readonly_clight_host fe observe) (dual_rect_domain row rows outer) (dual_rect_property d array row rows columns)
    (@dual_rect_tree d VALID fe O observe array row rows column columns body outer RC RN RM CN CM BODY OUTER).
Proof.
  eapply readonly_condition_entails.
  - eapply sequence_readonly_conditions with (A := clight_readonly_check_algebra fe observe).
    + exact (@dual_rect_setup_condition d VALID array row rows column columns body outer CM BODY OUTER fe O observe).
    + eapply readonly_condition_restrict.
      * exact (@synthesized_prefix_scan_condition clight_entry (readonly_clight_host fe observe) Z
          (clight_readonly_check_algebra fe observe) (clight_readonly_branch_algebra fe observe)
          (@dual_rect_outer_spec d VALID fe array row rows column columns body outer RC RN RM CN CM BODY OUTER O observe)
          (Z.to_nat (rectangle_outer_limit d)) 0).
      * intros entry [DOMAIN SETUP]; exact (@dual_rect_initial_cursor d VALID row rows column columns outer CM fe entry DOMAIN SETUP).
  - intros entry DOMAIN [SETUP SCAN]; split; [exact SETUP|].
    destruct SETUP as [ZERO [NR [MR DEFINED]]]; intros i j IR JR.
    eapply dual_rect_outer_scan_sound; [exact SCAN| |lia|exact JR].
    rewrite Z2Nat.id by (pose proof (rectangle_limits VALID); lia); lia.
Defined.

Print Assumptions dual_rect_domain_entry.
Print Assumptions dual_rect_columns_defined.
Print Assumptions dual_rect_setup_run.
Print Assumptions dual_rect_initial_cursor.
Print Assumptions dual_rect_condition.
