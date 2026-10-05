From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightRedundantSet ClightMatrixGuard ClightNoWrap
  ClightPureExpr ClightSameAddress ClightDecisionRule ClightCountedLoop ClightCountedProtocol
  ClightFrontendRegion ClightStraightLine ClightLoopExecution ClightLoopSyntax ClightTempFrame ClightRegionProgress
  ClightMatrixStore ClightMatrixLoops CompCertStoreSchedule.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyLoadedTreeSynthesis
  ClightStrictLoopProgress ClightStrictIteration ClightLoadedBoundSyntax ClightLoadedBoundGuard
  ClightLoadedMatrixSyntax ClightLoadedMatrixGuard ClightStableLoadBody ClightReadonlyCellSwap
  ClightDualLoadedMatrixPrefix ClightDualLoadedUnitSyntax ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition dual_matrix_aliases array rows columns points := fold_right
  (fun point tail => Test (loaded_matrix_alias_expr array rows point) (Decision false)
    (Test (loaded_matrix_alias_expr array columns point) (Decision false) tail)) (Decision true) points.
Definition dual_matrix_alias_accept array rows columns points entry := fold_right
  (fun point tail => negb (loaded_matrix_alias_flag array rows point entry) &&
    (negb (loaded_matrix_alias_flag array columns point entry) && tail)) true points.
Definition dual_matrix_guard array row rows columns := Test (register_guard row Int.zero)
  (Test (loaded_matrix_two_expr rows) (Test (loaded_matrix_two_expr columns)
    (dual_matrix_aliases array rows columns [0;1;2;3]) (Decision false)) (Decision false)) (Decision false).
Definition dual_matrix_accept array row rows columns entry := register_flag row Int.zero entry &&
  (loaded_matrix_two_flag rows entry && (loaded_matrix_two_flag columns entry &&
    dual_matrix_alias_accept array rows columns [0;1;2;3] entry)).
Definition dual_matrix_property array row rows columns entry := register_equals row Int.zero tt entry /\
  loaded_matrix_two_flag rows entry = true /\ loaded_matrix_two_flag columns entry = true /\
  forall point, 0 <= point <= 3 -> loaded_matrix_alias_flag array rows point entry = false /\
    loaded_matrix_alias_flag array columns point entry = false.

Lemma dual_matrix_load_after array rows columns entry block point value memory final q qo r ro :
  0 <= point <= 3 -> matrix_array_binding (entry_ge entry) (entry_env entry) array block ->
  (entry_temps entry) ! rows = Some (Vptr q qo) -> (entry_temps entry) ! columns = Some (Vptr r ro) ->
  loaded_matrix_alias_flag array rows point entry = false -> loaded_matrix_alias_flag array columns point entry = false ->
  Mem.loadv Mint32 memory (Vptr q qo) = Some (Vint (Int.repr 2)) ->
  Mem.loadv Mint32 memory (Vptr r ro) = Some (Vint (Int.repr 2)) ->
  store_action_run (matrix_cell block point value) memory final ->
  Mem.loadv Mint32 final (Vptr q qo) = Some (Vint (Int.repr 2)) /\
  Mem.loadv Mint32 final (Vptr r ro) = Some (Vint (Int.repr 2)).
Proof.
  intros RANGE ARRAY Q R AQ AR READ READ2 STORE; split; eapply mint32_load_survives_apart_store.
  - exact (@loaded_matrix_storev block point value memory final RANGE STORE).
  - exact READ.
  - exact (@loaded_matrix_alias_apart array rows point entry block q qo ARRAY Q AQ).
  - exact (@loaded_matrix_storev block point value memory final RANGE STORE).
  - exact READ2.
  - exact (@loaded_matrix_alias_apart array columns point entry block r ro ARRAY R AR).
Qed.

Section POINTS.
Variables array row rows column columns : ident.
Variables body outer : statement.
Hypothesis RC : row <> column.
Hypothesis RN : row <> rows.
Hypothesis RM : row <> columns.
Hypothesis CN : column <> rows.
Hypothesis CM : column <> columns.
Hypothesis BODY : flatten_region body = [matrix_store array row column].
Hypothesis OUTER : flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body].

Theorem dual_matrix_alias_run fe ge locals le memory q qo r ro after final :
  le ! row = Some (Vint Int.zero) -> le ! rows = Some (Vptr q qo) -> le ! columns = Some (Vptr r ro) ->
  Mem.loadv Mint32 memory (Vptr q qo) = Some (Vint (Int.repr 2)) ->
  Mem.loadv Mint32 memory (Vptr r ro) = Some (Vint (Int.repr 2)) ->
  exec_stmt fe ge locals le memory (dual_matrix_source row rows outer) E0 after final Out_normal ->
  decision_run (Entry ge locals le memory) (dual_matrix_aliases array rows columns [0;1;2;3])
    (dual_matrix_alias_accept array rows columns [0;1;2;3] (Entry ge locals le memory)).
Proof.
  intros I Q R READ READ2 SOURCE.
  destruct (@dual_matrix_open_row fe ge locals le memory array row rows column columns body outer 0 q qo after final
    BODY OUTER ltac:(lia) I Q READ SOURCE) as [exit0 [mem0 [next0 [nextmem0 [INNER0 [INC0 TAIL0]]]]]].
  assert (I0 : (PTree.set column (Vint Int.zero) le) ! row = Some (Vint (Int.repr 0)))
    by (rewrite PTree.gso by congruence; exact I).
  assert (R0 : (PTree.set column (Vint Int.zero) le) ! columns = Some (Vptr r ro))
    by (rewrite PTree.gso by congruence; exact R).
  destruct (@dual_matrix_inner_step fe ge locals _ memory array row column columns body 0 0 r ro exit0 mem0
    RC BODY ltac:(lia) ltac:(lia) I0 (PTree.gss _ _ _) R0 READ2 INNER0)
    as [block [m1 [ARRAY [S0 INNER1]]]].
  change (store_action_run (matrix_cell block 0 1) memory m1) in S0.
  rewrite PTree.set2 in INNER1.
  cbn [dual_matrix_aliases dual_matrix_alias_accept fold_right].
  eapply run_test; [eapply loaded_matrix_alias_test;
    [lia|exact ARRAY|exact Q|exact READ|eapply loaded_matrix_store_word; [lia|exact S0]]|].
  destruct (loaded_matrix_alias_flag array rows 0 (Entry ge locals le memory)) eqn:A0; cbn; [constructor|].
  eapply run_test; [eapply loaded_matrix_alias_test;
    [lia|exact ARRAY|exact R|exact READ2|eapply loaded_matrix_store_word; [lia|exact S0]]|].
  destruct (loaded_matrix_alias_flag array columns 0 (Entry ge locals le memory)) eqn:B0; cbn; [constructor|].
  destruct (@dual_matrix_load_after array rows columns (Entry ge locals le memory) block 0 1 memory m1 q qo r ro
    ltac:(lia) ARRAY Q R A0 B0 READ READ2 S0) as [READ1 READ21].
  assert (I1 : (PTree.set column (Vint (Int.repr 1)) le) ! row = Some (Vint (Int.repr 0)))
    by (rewrite PTree.gso by congruence; exact I).
  assert (R1 : (PTree.set column (Vint (Int.repr 1)) le) ! columns = Some (Vptr r ro))
    by (rewrite PTree.gso by congruence; exact R).
  destruct (@dual_matrix_inner_step fe ge locals _ m1 array row column columns body 0 1 r ro exit0 mem0
    RC BODY ltac:(lia) ltac:(lia) I1 (PTree.gss _ _ _) R1 READ21 INNER1)
    as [other [m2 [OTHER [S1 INNER2]]]].
  assert (SAME : block = other) by (eapply matrix_array_binding_unique; eassumption); subst other.
  change (store_action_run (matrix_cell block 1 2) m1 m2) in S1.
  rewrite PTree.set2 in INNER2.
  assert (WORD1 : writable_word memory block (Ptrofs.repr 4)).
  { eapply loaded_matrix_permission_back; [exact S0|exact (@loaded_matrix_store_word block 1 2 m1 m2 ltac:(lia) S1)]. }
  eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact Q|exact READ|exact WORD1]|].
  destruct (loaded_matrix_alias_flag array rows 1 (Entry ge locals le memory)) eqn:A1; cbn; [constructor|].
  eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact R|exact READ2|exact WORD1]|].
  destruct (loaded_matrix_alias_flag array columns 1 (Entry ge locals le memory)) eqn:B1; cbn; [constructor|].
  destruct (@dual_matrix_load_after array rows columns (Entry ge locals le memory) block 1 2 m1 m2 q qo r ro
    ltac:(lia) ARRAY Q R A1 B1 READ1 READ21 S1) as [READ3 READ23].
  assert (I2 : (PTree.set column (Vint (Int.repr 2)) le) ! row = Some (Vint (Int.repr 0)))
    by (rewrite PTree.gso by congruence; exact I).
  assert (R2 : (PTree.set column (Vint (Int.repr 2)) le) ! columns = Some (Vptr r ro))
    by (rewrite PTree.gso by congruence; exact R).
  pose proof (@dual_matrix_close_row fe ge locals _ m2 row rows column columns body outer 0 r ro
    exit0 mem0 next0 nextmem0 after final ltac:(lia) I2 (PTree.gss _ _ _) R2 READ23
    (@matrix_body_quiet array row column body BODY) INNER2 INC0 TAIL0) as ROW1.
  set (next := PTree.set row (Vint (Int.repr 1)) (PTree.set column (Vint (Int.repr 2)) le)).
  assert (QN : next ! rows = Some (Vptr q qo)) by (unfold next; rewrite !PTree.gso by congruence; exact Q).
  assert (RNEXT : next ! columns = Some (Vptr r ro)) by (unfold next; rewrite !PTree.gso by congruence; exact R).
  destruct (@dual_matrix_open_row fe ge locals next m2 array row rows column columns body outer 1 q qo after final
    BODY OUTER ltac:(lia) (PTree.gss _ _ _) QN READ3 ROW1)
    as [exit1 [mem1 [next1 [nextmem1 [INNER3 [INC1 TAIL1]]]]]].
  assert (I3 : (PTree.set column (Vint Int.zero) next) ! row = Some (Vint (Int.repr 1)))
    by (rewrite PTree.gso by congruence; unfold next; apply PTree.gss).
  assert (R3 : (PTree.set column (Vint Int.zero) next) ! columns = Some (Vptr r ro))
    by (rewrite PTree.gso by congruence; exact RNEXT).
  destruct (@dual_matrix_inner_step fe ge locals _ m2 array row column columns body 1 0 r ro exit1 mem1
    RC BODY ltac:(lia) ltac:(lia) I3 (PTree.gss _ _ _) R3 READ23 INNER3)
    as [other [m3 [OTHER2 [S2 INNER4]]]].
  assert (SAME : block = other) by (eapply matrix_array_binding_unique; eassumption); subst other.
  change (store_action_run (matrix_cell block 2 11) m2 m3) in S2.
  rewrite PTree.set2 in INNER4.
  assert (WORD2 : writable_word memory block (Ptrofs.repr 8)).
  { eapply loaded_matrix_permission_back; [exact S0|].
    eapply loaded_matrix_permission_back; [exact S1|exact (@loaded_matrix_store_word block 2 11 m2 m3 ltac:(lia) S2)]. }
  eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact Q|exact READ|exact WORD2]|].
  destruct (loaded_matrix_alias_flag array rows 2 (Entry ge locals le memory)) eqn:A2; cbn; [constructor|].
  eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact R|exact READ2|exact WORD2]|].
  destruct (loaded_matrix_alias_flag array columns 2 (Entry ge locals le memory)) eqn:B2; cbn; [constructor|].
  destruct (@dual_matrix_load_after array rows columns (Entry ge locals le memory) block 2 11 m2 m3 q qo r ro
    ltac:(lia) ARRAY Q R A2 B2 READ3 READ23 S2) as [READ4 READ24].
  assert (I4 : (PTree.set column (Vint (Int.repr 1)) next) ! row = Some (Vint (Int.repr 1)))
    by (rewrite PTree.gso by congruence; unfold next; apply PTree.gss).
  assert (R4 : (PTree.set column (Vint (Int.repr 1)) next) ! columns = Some (Vptr r ro))
    by (rewrite PTree.gso by congruence; exact RNEXT).
  destruct (@dual_matrix_inner_step fe ge locals _ m3 array row column columns body 1 1 r ro exit1 mem1
    RC BODY ltac:(lia) ltac:(lia) I4 (PTree.gss _ _ _) R4 READ24 INNER4)
    as [other [m4 [OTHER3 [S3 INNER5]]]].
  assert (SAME : block = other) by (eapply matrix_array_binding_unique; eassumption); subst other.
  change (store_action_run (matrix_cell block 3 12) m3 m4) in S3.
  assert (WORD3 : writable_word memory block (Ptrofs.repr 12)).
  { eapply loaded_matrix_permission_back; [exact S0|].
    eapply loaded_matrix_permission_back; [exact S1|].
    eapply loaded_matrix_permission_back; [exact S2|exact (@loaded_matrix_store_word block 3 12 m3 m4 ltac:(lia) S3)]. }
  eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact Q|exact READ|exact WORD3]|].
  destruct (loaded_matrix_alias_flag array rows 3 (Entry ge locals le memory)); cbn; [constructor|].
  eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact R|exact READ2|exact WORD3]|].
  destruct (loaded_matrix_alias_flag array columns 3 (Entry ge locals le memory)); constructor.
Qed.

Theorem dual_matrix_columns_entry entry : loaded_matrix_domain row rows outer entry ->
  register_flag row Int.zero entry = true -> loaded_matrix_two_flag rows entry = true ->
  loaded_bound_entry row columns entry.
Proof.
  intros DOMAIN ZERO TWO.
  destruct (@loaded_matrix_prefix_facts row rows outer entry DOMAIN ZERO TWO) as [q [qo [I [Q READ]]]].
  destruct DOMAIN as [ENTRY [after [final SOURCE]]]; destruct entry as [ge locals le memory]; cbn in I,Q,READ,SOURCE |- *.
  destruct (@dual_matrix_open_row (fun _ _ _ _ _ _ _ => False) ge locals le memory array row rows column columns
    body outer 0 q qo after final BODY OUTER ltac:(lia) I Q READ (SOURCE _))
    as [exit [mem [next [nextmem [INNER _]]]]].
  destruct (loaded_source_head INNER) as [flag TEST].
  destruct (loaded_bound_test_facts TEST) as [j [word [r [ro [J [R [READ2 _]]]]]]].
  rewrite PTree.gso in R by congruence; exists Int.zero,word,r,ro; repeat split; assumption.
Qed.

Theorem dual_matrix_guard_run entry : loaded_matrix_domain row rows outer entry ->
  decision_run entry (dual_matrix_guard array row rows columns) (dual_matrix_accept array row rows columns entry).
Proof.
  intro DOMAIN; destruct DOMAIN as [ENTRY [after [final SOURCE]]].
  assert (D : loaded_matrix_domain row rows outer entry) by (split; [exact ENTRY|eauto]).
  destruct ENTRY as [i [upper [q [qo [I [Q READ]]]]]].
  assert (ENTRY : loaded_bound_entry row rows entry) by (do 4 eexists; repeat split; eassumption).
  unfold dual_matrix_guard,dual_matrix_accept; eapply run_test; [apply register_expression_test; exists i; exact I|].
  destruct (register_flag row Int.zero entry) eqn:ZERO; cbn; [|constructor].
  eapply run_test; [exact (@loaded_matrix_two_test row rows entry ENTRY)|].
  destruct (loaded_matrix_two_flag rows entry) eqn:TWO; cbn; [|constructor].
  pose proof (dual_matrix_columns_entry D ZERO TWO) as M_ENTRY.
  eapply run_test; [exact (@loaded_matrix_two_test row columns entry M_ENTRY)|].
  destruct (loaded_matrix_two_flag columns entry) eqn:M_TWO; cbn; [|constructor].
  destruct (@loaded_matrix_prefix_facts row rows outer entry D ZERO TWO) as [q1 [qo1 [ROW [Q1 READ1]]]].
  destruct M_ENTRY as [x [word [r [ro [X [R READ2]]]]]].
  unfold loaded_matrix_two_flag,loaded_matrix_upper in M_TWO; rewrite R,READ2 in M_TWO;
    apply Int.same_if_eq in M_TWO; subst word.
  destruct entry as [ge locals le memory]; cbn in ROW,Q1,READ1,R,READ2,SOURCE |- *.
  exact (@dual_matrix_alias_run (fun _ _ _ _ _ _ _ => False) ge locals le memory q1 qo1 r ro after final
    ROW Q1 R READ1 READ2 (SOURCE _)).
Qed.
End POINTS.

Lemma dual_matrix_alias_accept_sound array rows columns points entry :
  dual_matrix_alias_accept array rows columns points entry = true ->
  forall point, In point points -> loaded_matrix_alias_flag array rows point entry = false /\
    loaded_matrix_alias_flag array columns point entry = false.
Proof.
  induction points as [|first points IH]; cbn [dual_matrix_alias_accept fold_right]; [intros _ point BAD; contradiction|].
  rewrite !andb_true_iff; intros [R [C REST]] point [HERE|LATER].
  - subst point; apply negb_true_iff in R,C; auto.
  - apply IH; assumption.
Qed.
Lemma dual_matrix_guard_sound array row rows columns outer entry : loaded_matrix_domain row rows outer entry ->
  dual_matrix_accept array row rows columns entry = true -> dual_matrix_property array row rows columns entry.
Proof.
  intros [[i [upper [q [qo [I REST]]]]] COMPLETE] ACCEPT.
  unfold dual_matrix_accept in ACCEPT; repeat rewrite andb_true_iff in ACCEPT; destruct ACCEPT as [ZERO [N [M ALIASES]]].
  split; [apply register_flag_evidence; [exists i; exact I|exact ZERO]|split; [exact N|split; [exact M|]]].
  intros point RANGE; apply (@dual_matrix_alias_accept_sound array rows columns [0;1;2;3] entry ALIASES).
  assert (point=0 \/ point=1 \/ point=2 \/ point=3) by lia; destruct H as [H|[H|[H|H]]]; subst point; cbn; tauto.
Qed.
Definition dual_matrix_condition fe O (observe : fragment_observation -> O -> Prop) array row rows column columns body outer
  (RC : row <> column) (RN : row <> rows) (RM : row <> columns) (CN : column <> rows) (CM : column <> columns)
  (BODY : flatten_region body = [matrix_store array row column])
  (OUTER : flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body]) :
  readonly_condition (readonly_clight_host fe observe) (loaded_matrix_domain row rows outer)
    (dual_matrix_property array row rows columns) (dual_matrix_guard array row rows columns).
Proof.
  constructor.
  - intros entry DOMAIN; eapply readonly_decision_run_safe;
      exact (@dual_matrix_guard_run array row rows column columns body outer RC RN RM CN CM BODY OUTER entry DOMAIN).
  - intros entry DOMAIN; exists (dual_matrix_accept array row rows columns entry),entry; split; [|reflexivity].
    exact (@dual_matrix_guard_run array row rows column columns body outer RC RN RM CN CM BODY OUTER entry DOMAIN).
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    apply dual_matrix_guard_sound with (outer := outer); [exact DOMAIN|].
    symmetry; eapply readonly_decision_determinate; [exact RUN|].
    exact (@dual_matrix_guard_run array row rows column columns body outer RC RN RM CN CM BODY OUTER entry DOMAIN).
Defined.

Print Assumptions dual_matrix_load_after.
Print Assumptions dual_matrix_alias_run.
Print Assumptions dual_matrix_columns_entry.
Print Assumptions dual_matrix_guard_run.
Print Assumptions dual_matrix_guard_sound.
Print Assumptions dual_matrix_condition.
