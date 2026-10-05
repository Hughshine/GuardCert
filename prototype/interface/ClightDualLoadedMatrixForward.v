From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightRedundantSet ClightNoWrap ClightPureExpr
  ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution
  ClightLoopSyntax ClightStraightLine ClightTempFrame ClightTempFootprint ClightProjectedExecution
  ClightRegionProgress ClightMatrixStore ClightMatrixLoops CompCertStoreSchedule CompCertMemoryEquivalence.
From GuardInterface Require Import ClightReadonlyRewrite ClightLoadedBoundSyntax ClightLoadedBoundGuard
  ClightLoadedMatrixSyntax ClightLoadedMatrixGuard ClightStableLoopCondition ClightQuietDeterminacy
  ClightDualLoadedMatrixPrefix ClightDualLoadedMatrixGuard ClightDualLoadedMatrixLoop
  ClightRegionBoundary ClightReadonlyProjectedCompiler ClightDualLoadedUnitSyntax ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem dual_matrix_domain_from_source fe ge locals le memory array row rows column columns body outer after final :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body] ->
  exec_stmt fe ge locals le memory (dual_matrix_source row rows outer) E0 after final Out_normal ->
  loaded_matrix_domain row rows outer (Entry ge locals le memory).
Proof.
  intros BODY OUTER SOURCE; split.
  - destruct (loaded_source_head SOURCE) as [flag TEST].
    destruct (loaded_bound_test_facts TEST) as [i [upper [q [qo [I [Q [READ _]]]]]]]; do 4 eexists; repeat split; eassumption.
  - exists after,final; intro other; eapply (@quiet_execution_preserved fe other ge ge);
      [split; [reflexivity|intros; reflexivity]|exact SOURCE|].
    exact (@dual_matrix_source_quiet array row rows column columns body outer BODY OUTER).
Qed.

Theorem dual_matrix_forward fe live array row rows column columns cache body outer entry observed :
  row <> column -> row <> rows -> row <> columns -> column <> rows -> column <> columns ->
  cache <> row -> cache <> column -> cache <> rows -> cache <> columns -> ~ In cache live ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body] ->
  loaded_matrix_domain row rows outer entry -> dual_matrix_property array row rows columns entry ->
  clight_fragment_run fe (dual_matrix_source row rows outer) entry observed ->
  exists transformed, clight_fragment_run fe (dual_matrix_candidate array row rows column cache) entry transformed /\
    boundary_observe (public_exit_ports live) observed transformed.
Proof.
  intros RC RN RM CN CM CR CC CQ CK FRESH BODY OUTER DOMAIN [ZERO [TWO [M_TWO ALIASES]]] SOURCE.
  assert (ZERO_FLAG : register_flag row Int.zero entry = true).
  { unfold register_flag,temp_word; unfold register_equals in ZERO; rewrite ZERO; apply Int.eq_true. }
  pose proof (@dual_matrix_columns_entry array row rows column columns body outer RC RN RM CN CM BODY OUTER
    entry DOMAIN ZERO_FLAG TWO) as M_ENTRY.
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  pose proof (@dual_matrix_source_quiet array row rows column columns body outer BODY OUTER) as QUIET.
  pose proof (@quiet_execution_silent fe ge locals le memory _ trace after final outcome SOURCE QUIET) as SILENT; subst trace.
  assert (NORMAL : outcome = Out_normal).
  { eapply normal_statement_execution; [|exact SOURCE].
    cbn [dual_matrix_source loaded_bound_loop strict_frontend_loop normal_statement quiet_statement counter_increment] in QUIET |- *.
    exact QUIET. }
  subst outcome.
  destruct DOMAIN as [[i [upper [q [qo [I [Q READ]]]]]] COMPLETE].
  destruct M_ENTRY as [x [word [r [ro [X [R READ2]]]]]].
  unfold loaded_matrix_two_flag,loaded_matrix_upper in TWO,M_TWO; cbn [entry_temps entry_memory] in *;
    rewrite Q,READ in TWO; rewrite R,READ2 in M_TWO;
    apply Int.same_if_eq in TWO; apply Int.same_if_eq in M_TWO; subst upper word.
  change (le ! row = Some (Vint (Int.repr 0))) in ZERO.
  destruct (@dual_matrix_open_row fe ge locals le memory array row rows column columns body outer 0 q qo after final
    BODY OUTER ltac:(lia) ZERO Q READ SOURCE) as [exit [mem [next [nextmem [INNER _]]]]].
  assert (RI : (PTree.set column (Vint Int.zero) le) ! row = Some (Vint (Int.repr 0)))
    by (rewrite PTree.gso by congruence; exact ZERO).
  assert (RMEM : (PTree.set column (Vint Int.zero) le) ! columns = Some (Vptr r ro))
    by (rewrite PTree.gso by congruence; exact R).
  destruct (@dual_matrix_inner_step fe ge locals _ memory array row column columns body 0 0 r ro exit mem
    RC BODY ltac:(lia) ltac:(lia) RI (PTree.gss _ _ _) RMEM READ2 INNER) as [block [middle [ARRAY PREFIX]]].
  assert (APART : forall point, 0 <= point <= 3 -> Vptr block (Ptrofs.repr (4*point)) <> Vptr q qo /\
    Vptr block (Ptrofs.repr (4*point)) <> Vptr r ro).
  { intros point RANGE; destruct (ALIASES point RANGE) as [A B]; split.
    - exact (@loaded_matrix_alias_apart array rows point (Entry ge locals le memory) block q qo ARRAY Q A).
    - exact (@loaded_matrix_alias_apart array columns point (Entry ge locals le memory) block r ro ARRAY R B). }
  assert (BODY_SCOPE : ~ In cache (statement_temps body)).
  { rewrite <- (flatten_statement_temps body); rewrite BODY.
    cbn [concat map statement_temps expression_temps matrix_store matrix_lvalue matrix_index matrix_value matrix_constant];
      repeat rewrite in_app_iff; cbn; intuition congruence. }
  assert (OUTER_SCOPE : ~ In cache (statement_temps outer)).
  { rewrite <- (flatten_statement_temps outer); rewrite OUTER.
    cbn [concat map statement_temps expression_temps matrix_reset matrix_constant loaded_bound_loop strict_frontend_loop
      loaded_bound_test signed_load signed_pointer_temp counter_increment]; repeat rewrite in_app_iff; cbn; intuition congruence. }
  assert (PRIVATE : ~ In cache (statement_temps (dual_matrix_source row rows outer) ++ live)).
  { cbn [dual_matrix_source loaded_bound_loop strict_frontend_loop statement_temps expression_temps
      loaded_bound_test signed_load signed_pointer_temp counter_increment]; repeat rewrite in_app_iff; cbn; intuition congruence. }
  set (target := PTree.set cache (Vint (Int.repr 2)) le).
  destruct (@structured_execution_temp_transport fe ge locals le memory (dual_matrix_source row rows outer)
    E0 after final Out_normal SOURCE (statement_temps (dual_matrix_source row rows outer) ++ live) target [row;column]
    (@dual_matrix_source_writes array row rows column columns body outer BODY OUTER)
    ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN)
    (@temp_agree_set (statement_temps (dual_matrix_source row rows outer) ++ live) le cache (Vint (Int.repr 2)) PRIVATE))
    as [target_after [TRANSPORT PUBLIC]].
  assert (INV : dual_matrix_outer_snapshot 2 row rows columns cache q qo r ro target memory).
  { exists 0; split; [lia|split; [unfold target; rewrite PTree.gso by congruence; exact ZERO|]].
    unfold dual_matrix_values,target; repeat split; repeat rewrite PTree.gso by congruence;
      auto using PTree.gss. }
  destruct (@dual_matrix_outer_cached fe ge locals array row rows column columns cache body outer block q qo r ro
    target memory E0 target_after final Out_normal RC RN RM CN CM CR CC BODY OUTER ARRAY APART INV TRANSPORT)
    as [CACHED _].
  assert (TARGET_ROW : target ! row = Some (Vint (Int.repr 0))) by (unfold target; rewrite PTree.gso by congruence; exact ZERO).
  assert (TARGET_CACHE : target ! cache = Some (Vint (Int.repr 2))) by (unfold target; apply PTree.gss).
  destruct (@matrix_source_decode fe ge locals target memory array row cache column cache body
    (Ssequence (matrix_reset column) (frontend_counted_loop column cache body)) target_after final
    ltac:(congruence) RC CC ltac:(congruence) ltac:(congruence) BODY eq_refl TARGET_ROW TARGET_CACHE TARGET_CACHE CACHED)
    as [other [OTHER [SCHEDULE EXIT]]].
  assert (SAME : block = other) by (eapply matrix_array_binding_unique; eassumption); subst other.
  apply matrix_interchange_preserves_actual_memory in SCHEDULE.
  exists (FragmentObservation E0 target_after final Out_normal); split.
  - unfold clight_fragment_run,dual_matrix_candidate; cbn.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := target) (m1 := memory).
    + unfold target; constructor; apply eval_Elvalue with (loc := q) (ofs := qo) (bf := Full).
      * apply eval_Ederef,eval_Etempvar; exact Q.
      * apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
    + rewrite EXIT; eapply matrix_target_encode; eauto.
  - unfold boundary_observe; cbn; split; [reflexivity|split; [reflexivity|split]].
    + eapply temp_agree_weaken; [|apply temp_agree_sym; exact PUBLIC]; intros id IN; apply in_or_app; right; exact IN.
    + apply memory_equivalent_refl.
Qed.
Print Assumptions dual_matrix_domain_from_source.
Print Assumptions dual_matrix_forward.
