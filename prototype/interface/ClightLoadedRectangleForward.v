From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightLoopExecution ClightStraightLine ClightTempFrame ClightTempFootprint
  ClightProjectedExecution ClightLoopSyntax ClightRegionProgress ClightRectangularStore ClightRectangularGuard
  ClightRectangularLoops ClightRectangularRegion CompCertMemoryEquivalence.
From GuardInterface Require Import ClightReadonlyRewrite ClightLoadedBoundSyntax ClightStrictLoopProgress ClightStableLoopCondition
  ClightReadonlyLoadedTreeSynthesis ClightQuietDeterminacy ClightRegionBoundary ClightReadonlyProjectedCompiler
  ClightLoadedRectangleRow ClightLoadedRectangleMemory ClightLoadedRectangleAtoms ClightLoadedRectanglePrefix ClightLoadedRectangleGuard ClightLoadedRectangleLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma loaded_rectangle_constant_temps value : expression_temps (rect_constant value) = [].
Proof. unfold rect_constant; destruct (value <? 0); reflexivity. Qed.

Theorem loaded_rectangle_forward d (VALID : rectangle_layout_valid d) fe live
  array row bound column columns cache body outer_body entry observed :
  row <> bound -> row <> column -> bound <> column -> row <> columns -> column <> columns ->
  cache <> row -> cache <> bound -> cache <> column -> cache <> columns -> ~ In cache live ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_rectangle_domain row bound outer_body entry -> loaded_rectangle_property d array row bound columns entry ->
  clight_fragment_run fe (loaded_rectangle_source row bound outer_body) entry observed ->
  exists transformed,
    clight_fragment_run fe (loaded_rectangle_candidate d array row bound column columns cache) entry transformed /\
    boundary_observe (public_exit_ports live) observed transformed.
Proof.
  intros RQ RC QC RM CM CR CB CC CK FRESH BODY OUTER DOMAIN [SETUP ALIASES] SOURCE.
  pose proof (@loaded_rectangle_initial_prefix d VALID fe array row bound column columns body outer_body entry
    RQ RC QC RM CM BODY OUTER DOMAIN SETUP) as PREFIX.
  destruct PREFIX as [IR PREFIX].
  destruct PREFIX as [u [M [block [p [ofs [current [mem [exit [final' PREFIX]]]]]]]]].
  destruct PREFIX as [NR' [MR' [COLS' [ARRAY REST]]]].
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  pose proof (@loaded_rectangle_source_quiet d array row bound column columns body outer_body BODY OUTER) as QUIET.
  pose proof (@quiet_execution_silent fe ge locals le memory _ trace after final outcome SOURCE QUIET) as SILENT.
  pose proof (@quiet_loop_normal fe ge locals le memory _ _ trace after final outcome QUIET SOURCE) as NORMAL.
  subst trace outcome.
  destruct SETUP as [ZERO [NR [[m COLS] MR]]].
  destruct DOMAIN as [[iterator [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE].
  cbn [entry_temps entry_memory entry_ge entry_env] in ZERO, BOUND, READ, ITER, COLS, ARRAY, COLS'.
  unfold loaded_rectangle_word in NR; cbn [entry_temps entry_memory] in NR; rewrite BOUND, READ in NR.
  unfold temp_word in MR; cbn [entry_temps] in MR; rewrite COLS in MR.
  assert (COLS_REPR : le ! columns = Some (Vint (Int.repr (Int.signed m)))) by (rewrite Int.repr_signed; exact COLS).
  assert (APART : forall i j, 0 <= i < Int.signed upper -> 0 <= j < Int.signed m ->
      Vptr block (loaded_rectangle_offset d i j) <> Vptr q qofs).
  { intros i j I J; eapply (@loaded_rectangle_alias_apart d array bound i j (Entry ge locals le memory) block q qofs);
      [exact ARRAY|exact BOUND|].
    apply (ALIASES i); [unfold loaded_rectangle_word; cbn [entry_temps entry_memory]; rewrite BOUND, READ; exact I|].
    unfold temp_word; cbn [entry_temps]; rewrite COLS; exact J. }
  assert (BODY_SCOPE : ~ In cache (statement_temps body)).
  { rewrite <- (flatten_statement_temps body); rewrite BODY.
    cbn [concat map statement_temps expression_temps rect_store rect_lvalue rect_index rect_value].
    repeat rewrite loaded_rectangle_constant_temps.
    repeat rewrite in_app_iff; cbn; intuition congruence. }
  assert (OUTER_SCOPE : ~ In cache (statement_temps outer_body)).
  { rewrite <- (flatten_statement_temps outer_body); rewrite OUTER.
    cbn [concat map statement_temps expression_temps rectangle_reset rect_constant
      frontend_counted_loop counter_condition counter_increment].
    repeat rewrite in_app_iff; cbn; intuition congruence. }
  assert (PRIVATE : ~ In cache (statement_temps (loaded_rectangle_source row bound outer_body) ++ live)).
  { cbn [loaded_rectangle_source loaded_bound_loop strict_frontend_loop statement_temps expression_temps
      loaded_bound_test signed_load signed_pointer_temp counter_increment].
    repeat rewrite in_app_iff; cbn; intuition congruence. }
  set (target := PTree.set cache (Vint upper) le).
  destruct (@structured_execution_temp_transport fe ge locals le memory (loaded_rectangle_source row bound outer_body)
    E0 after final Out_normal SOURCE (statement_temps (loaded_rectangle_source row bound outer_body) ++ live)
    target [row;column] (@loaded_rectangle_writes d array row bound column columns body outer_body BODY OUTER)
    ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN)
    (@temp_agree_set (statement_temps (loaded_rectangle_source row bound outer_body) ++ live) le cache (Vint upper) PRIVATE))
    as [target_after [TRANSPORT PUBLIC]].
  assert (INV : loaded_rectangle_snapshot (Int.signed upper) row bound columns cache q qofs upper (Int.signed m) target memory).
  { unfold target; exists 0; split; [lia|].
    repeat split; try (rewrite PTree.gso by congruence); auto using PTree.gss. }
  pose proof (@loaded_rectangle_cached d VALID fe ge locals array row bound column columns cache body outer_body block q qofs
    upper (Int.signed m) target memory E0 target_after final Out_normal RQ RC QC RM CM CR CC BODY OUTER ARRAY NR MR APART INV TRANSPORT)
    as CACHED.
  assert (TARGET_ROW : target ! row = Some (Vint Int.zero)) by (unfold target; rewrite PTree.gso by congruence; exact ZERO).
  assert (TARGET_CACHE : target ! cache = Some (Vint (Int.repr (Int.signed upper))))
    by (unfold target; rewrite Int.repr_signed; apply PTree.gss).
  assert (TARGET_COLS : target ! columns = Some (Vint (Int.repr (Int.signed m))))
    by (unfold target; rewrite PTree.gso by congruence; exact COLS_REPR).
  pose proof (@rectangle_local d VALID array row cache column columns body outer_body
    ltac:(congruence) RC CC RM CM BODY OUTER fe ge locals target memory target_after final (Int.signed upper) (Int.signed m)
    TARGET_ROW TARGET_CACHE TARGET_COLS (Int.signed_range upper) (Int.signed_range m) NR MR CACHED) as SWAPPED.
  exists (FragmentObservation E0 target_after final Out_normal); split.
  - unfold clight_fragment_run, loaded_rectangle_candidate; cbn.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := target) (m1 := memory); [|exact SWAPPED].
    unfold target; constructor; apply eval_Elvalue with (loc := q) (ofs := qofs) (bf := Full).
    + apply eval_Ederef, eval_Etempvar; exact BOUND.
    + apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
  - unfold boundary_observe; cbn; split; [reflexivity|split; [reflexivity|split]].
    + eapply temp_agree_weaken; [|apply temp_agree_sym; exact PUBLIC].
      intros id IN; apply in_or_app; right; exact IN.
    + apply memory_equivalent_refl.
Qed.
Print Assumptions loaded_rectangle_forward.
