From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightLoopExecution ClightStraightLine ClightTempFrame ClightTempFootprint
  ClightProjectedExecution ClightLoopSyntax ClightRegionProgress ClightMatrixStore ClightMatrixLoops
  CompCertStoreSchedule CompCertMemoryEquivalence.
From GuardInterface Require Import ClightReadonlyRewrite ClightLoadedBoundSyntax ClightLoadedMatrixSyntax ClightLoadedMatrixGuard
  ClightStrictLoopProgress ClightStrictIteration ClightActiveLoopCondition ClightReadonlyLoadedTreeSynthesis
  ClightStableLoadBody ClightStableLoopCondition ClightQuietDeterminacy ClightRegionBoundary ClightReadonlyProjectedCompiler.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_matrix_snapshot limit row bound columns cache q qofs le memory :=
  exists point, 0 <= point <= limit /\ le ! row = Some (Vint (Int.repr point)) /\
    le ! bound = Some (Vptr q qofs) /\ le ! columns = Some (Vint (Int.repr 2)) /\
    le ! cache = Some (Vint (Int.repr 2)) /\ Mem.loadv Mint32 memory (Vptr q qofs) = Some (Vint (Int.repr 2)).
Lemma loaded_matrix_snapshot_weaken row bound columns cache q qofs le memory :
  loaded_matrix_snapshot 1 row bound columns cache q qofs le memory ->
  loaded_matrix_snapshot 2 row bound columns cache q qofs le memory.
Proof. intros [point [RANGE FACTS]]; exists point; split; [lia|exact FACTS]. Qed.

Theorem loaded_matrix_body_snapshot fe ge locals array row bound column columns cache body outer_body block q qofs
  le memory trace after final outcome : row <> column -> column <> bound -> column <> columns -> cache <> column ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  matrix_array_binding ge locals array block ->
  (forall point, 0 <= point <= 3 -> Vptr block (Ptrofs.repr (4*point)) <> Vptr q qofs) ->
  loaded_matrix_snapshot 2 row bound columns cache q qofs le memory ->
  expression_test (loaded_bound_test row bound) (Entry ge locals le memory) true ->
  exec_stmt fe ge locals le memory outer_body trace after final outcome ->
  loaded_matrix_snapshot 1 row bound columns cache q qofs after final.
Proof.
  intros RC CQ CM CC BODY OUTER ARRAY APART [point [RANGE [ROW [BOUND [COLS [CACHE READ]]]]]] ACTIVE RUN.
  assert (LT : Int.lt (Int.repr point) (Int.repr 2) = true).
  { eapply readonly_test_determinate; [eapply loaded_bound_test_eval; eassumption|exact ACTIVE]. }
  assert (SMALL : 0 <= point <= 1).
  { unfold Int.lt in LT; rewrite !Int.signed_repr in LT by
      (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
    destruct (zlt point 2); cbn in LT; [lia|discriminate]. }
  assert (QUIET : quiet_statement outer_body = true).
  { apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
    cbn [frontend_counted_loop quiet_statement counter_increment]; rewrite (@matrix_body_quiet array row column body BODY); reflexivity. }
  pose proof (@quiet_execution_silent fe ge locals le memory outer_body trace after final outcome RUN QUIET) as SILENT.
  pose proof (@normal_statement_execution fe ge locals outer_body
    (@matrix_outer_body_normal array row column columns body outer_body BODY OUTER) le memory trace after final outcome RUN) as NORMAL.
  subst trace outcome.
  destruct (@matrix_row_body_decode fe ge locals le memory array row column columns body outer_body point after final
    RC CM BODY OUTER ROW COLS SMALL RUN) as [other [middle [OTHER [FIRST [SECOND TEMPS]]]]].
  assert (SAME : block = other) by (eapply matrix_array_binding_unique; eassumption); subst other.
  assert (READ1 : Mem.loadv Mint32 middle (Vptr q qofs) = Some (Vint (Int.repr 2))).
  { eapply mint32_load_survives_apart_store.
    - exact (@loaded_matrix_storev block (point*2+0) (point*10+0+1) memory middle ltac:(lia) FIRST).
    - exact READ.
    - apply APART; lia. }
  assert (READ2 : Mem.loadv Mint32 final (Vptr q qofs) = Some (Vint (Int.repr 2))).
  { eapply mint32_load_survives_apart_store.
    - exact (@loaded_matrix_storev block (point*2+1) (point*10+1+1) middle final ltac:(lia) SECOND).
    - exact READ1.
    - apply APART; lia. }
  subst after; exists point; split; [exact SMALL|].
  repeat split; try (rewrite PTree.gso by congruence); assumption.
Qed.
Lemma loaded_matrix_increment_snapshot fe ge locals row bound columns cache q qofs le memory trace after final outcome :
  row <> bound -> row <> columns -> cache <> row ->
  loaded_matrix_snapshot 1 row bound columns cache q qofs le memory ->
  exec_stmt fe ge locals le memory (Ssequence Sskip (counter_increment row)) trace after final outcome ->
  loaded_matrix_snapshot 2 row bound columns cache q qofs after final.
Proof.
  intros RQ RM CR [point [RANGE [ROW [BOUND [COLS [CACHE READ]]]]]] RUN.
  destruct (@strict_increment_execution_exact fe ge locals row le memory trace after final outcome
    ltac:(exists (Int.repr point); split; [exact ROW|rewrite Int.signed_repr; change Int.max_signed with 2147483647;
      change Int.min_signed with (-2147483648); lia]) RUN) as [_ [TEMPS [MEMORY _]]]; subst after final.
  unfold increment_temps; rewrite ROW, Int.add_signed, Int.signed_repr by
    (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  change (Int.signed Int.one) with 1; exists (point+1); split; [lia|].
  split; [apply PTree.gss|repeat split; try (rewrite PTree.gso by congruence); assumption].
Qed.
Theorem loaded_matrix_cached fe ge locals array row bound column columns cache body outer_body block q qofs
  le memory trace after final outcome : row <> column -> row <> bound -> row <> columns ->
  column <> bound -> column <> columns -> cache <> row -> cache <> column ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  matrix_array_binding ge locals array block ->
  (forall point, 0 <= point <= 3 -> Vptr block (Ptrofs.repr (4*point)) <> Vptr q qofs) ->
  loaded_matrix_snapshot 2 row bound columns cache q qofs le memory ->
  exec_stmt fe ge locals le memory (loaded_matrix_source row bound outer_body) trace after final outcome ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row cache outer_body) trace after final outcome.
Proof.
  intros RC RQ RM CQ CM CR CC BODY OUTER ARRAY APART INV SOURCE.
  exact (proj1 (@strict_active_condition_transport fe ge locals row
    (loaded_bound_test row bound) (counter_condition row cache) outer_body
    (loaded_matrix_snapshot 2 row bound columns cache q qofs) (loaded_matrix_snapshot 1 row bound columns cache q qofs)
    ltac:(intros before mem flag [point [RANGE [ROW [BOUND [COLS [CACHE READ]]]]]] TEST;
      eapply loaded_bound_cached_test; eassumption)
    (fun before mem tr exit mem' out' INV TEST RUN => @loaded_matrix_body_snapshot fe ge locals
      array row bound column columns cache body outer_body block q qofs before mem tr exit mem' out'
      RC CQ CM CC BODY OUTER ARRAY APART INV TEST RUN)
    (@loaded_matrix_snapshot_weaken row bound columns cache q qofs)
    (fun before mem tr exit mem' out' INV RUN => @loaded_matrix_increment_snapshot fe ge locals row bound columns cache q qofs
      before mem tr exit mem' out' RQ RM CR INV RUN)
    le memory trace after final outcome SOURCE INV)).
Qed.
Print Assumptions loaded_matrix_body_snapshot.
Print Assumptions loaded_matrix_cached.

Theorem loaded_matrix_forward fe live array row bound column columns cache body outer_body entry observed :
  row <> column -> row <> bound -> row <> columns -> column <> bound -> column <> columns ->
  cache <> row -> cache <> bound -> cache <> column -> cache <> columns -> ~ In cache live ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  loaded_matrix_domain row bound outer_body entry -> loaded_matrix_property row bound columns array entry ->
  clight_fragment_run fe (loaded_matrix_source row bound outer_body) entry observed ->
  exists transformed,
    clight_fragment_run fe (loaded_matrix_candidate row bound column columns array cache) entry transformed /\
    boundary_observe (public_exit_ports live) observed transformed.
Proof.
  intros RC RQ RM CQ CM CR CB CC CK FRESH BODY OUTER DOMAIN [ZERO [TWO [COLS ALIASES]]] SOURCE.
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  pose proof (@loaded_matrix_source_quiet array row bound column columns body outer_body BODY OUTER) as QUIET.
  pose proof (@quiet_execution_silent fe ge locals le memory _ trace after final outcome SOURCE QUIET) as SILENT.
  assert (NORMAL : outcome = Out_normal).
  { eapply normal_statement_execution; [|exact SOURCE].
    cbn [loaded_matrix_source loaded_bound_loop strict_frontend_loop normal_statement quiet_statement counter_increment] in QUIET |- *.
    exact QUIET. }
  subst trace outcome.
  destruct DOMAIN as [[i [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE].
  cbn [entry_temps entry_memory] in BOUND, READ, ITER.
  unfold loaded_matrix_two_flag, loaded_matrix_upper in TWO; cbn [entry_temps entry_memory] in TWO;
    rewrite BOUND, READ in TWO; apply Int.same_if_eq in TWO; subst upper.
  change (le ! row = Some (Vint (Int.repr 0))) in ZERO.
  change (le ! columns = Some (Vint (Int.repr 2))) in COLS.
  cbn [entry_temps entry_memory] in BOUND, READ.
  destruct (@loaded_matrix_row_step fe ge locals le memory array row bound column columns body outer_body after final 0 q qofs
    RC CM BODY OUTER ltac:(lia) ZERO BOUND READ COLS SOURCE)
    as [block [middle [row_memory [ARRAY PREFIX]]]].
  assert (APART : forall point, 0 <= point <= 3 -> Vptr block (Ptrofs.repr (4*point)) <> Vptr q qofs).
  { intros point RANGE; exact (@loaded_matrix_alias_apart array bound point (Entry ge locals le memory)
      block q qofs ARRAY BOUND (ALIASES point RANGE)). }
  assert (BODY_SCOPE : ~ In cache (statement_temps body)).
  { rewrite <- (flatten_statement_temps body); rewrite BODY.
    cbn [concat map statement_temps expression_temps matrix_store matrix_lvalue matrix_index matrix_value matrix_constant].
    repeat rewrite in_app_iff; cbn; intuition congruence. }
  assert (OUTER_SCOPE : ~ In cache (statement_temps outer_body)).
  { rewrite <- (flatten_statement_temps outer_body); rewrite OUTER.
    cbn [concat map statement_temps expression_temps matrix_reset matrix_constant frontend_counted_loop counter_condition counter_increment].
    repeat rewrite in_app_iff; cbn; intuition congruence. }
  assert (PRIVATE : ~ In cache (statement_temps (loaded_matrix_source row bound outer_body) ++ live)).
  { cbn [loaded_matrix_source loaded_bound_loop strict_frontend_loop statement_temps expression_temps
      loaded_bound_test signed_load signed_pointer_temp counter_increment].
    repeat rewrite in_app_iff; cbn; intuition congruence. }
  set (target := PTree.set cache (Vint (Int.repr 2)) le).
  destruct (@structured_execution_temp_transport fe ge locals le memory (loaded_matrix_source row bound outer_body)
    E0 after final Out_normal SOURCE (statement_temps (loaded_matrix_source row bound outer_body) ++ live)
    target [row;column] (@loaded_matrix_writes array row bound column columns body outer_body BODY OUTER)
    ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN)
    (@temp_agree_set (statement_temps (loaded_matrix_source row bound outer_body) ++ live) le cache (Vint (Int.repr 2)) PRIVATE))
    as [target_after [TRANSPORT PUBLIC]].
  assert (INV : loaded_matrix_snapshot 2 row bound columns cache q qofs target memory).
  { unfold target; exists 0; split; [lia|].
    repeat split; try (rewrite PTree.gso by congruence); auto using PTree.gss. }
  pose proof (@loaded_matrix_cached fe ge locals array row bound column columns cache body outer_body block q qofs
    target memory E0 target_after final Out_normal RC RQ RM CQ CM CR CC BODY OUTER ARRAY APART INV TRANSPORT) as CACHED.
  assert (TARGET_ROW : target ! row = Some (Vint (Int.repr 0))) by (unfold target; rewrite PTree.gso by congruence; exact ZERO).
  assert (TARGET_CACHE : target ! cache = Some (Vint (Int.repr 2))) by (unfold target; apply PTree.gss).
  assert (TARGET_COLS : target ! columns = Some (Vint (Int.repr 2))) by (unfold target; rewrite PTree.gso by congruence; exact COLS).
  destruct (@matrix_source_decode fe ge locals target memory array row cache column columns body outer_body target_after final
    ltac:(congruence) RC CC RM CM BODY OUTER TARGET_ROW TARGET_CACHE TARGET_COLS CACHED)
    as [other [OTHER_ARRAY [SCHEDULE EXIT]]].
  assert (SAME : block = other) by (eapply matrix_array_binding_unique; eassumption); subst other.
  apply matrix_interchange_preserves_actual_memory in SCHEDULE.
  exists (FragmentObservation E0 target_after final Out_normal); split.
  - unfold clight_fragment_run, loaded_matrix_candidate; cbn.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := target) (m1 := memory).
    + unfold target; constructor.
      apply eval_Elvalue with (loc := q) (ofs := qofs) (bf := Full).
      * apply eval_Ederef, eval_Etempvar; exact BOUND.
      * apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
    + rewrite EXIT; eapply matrix_target_encode; eauto.
  - unfold boundary_observe; cbn; split; [reflexivity|split; [reflexivity|split]].
    + eapply temp_agree_weaken; [|apply temp_agree_sym; exact PUBLIC].
      intros id IN; apply in_or_app; right; exact IN.
    + apply memory_equivalent_refl.
Qed.
Print Assumptions loaded_matrix_forward.
