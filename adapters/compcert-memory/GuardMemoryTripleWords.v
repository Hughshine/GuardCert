From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightCountedLoop ClightCountedProtocol
  ClightTempFrame ClightLoopSyntax ClightStraightLine ClightRegionProgress ClightFrontendLoopProtocol
  ClightFrontendRegion ClightLoopExecution ClightRectangularStore ClightRectangularLoops ClightRedundantSet ClightZeroTrip ClightFramedLoop.
From GuardMemory Require Import GuardMemoryTripleSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_reset_child_normal body iterator child :
  flatten_region body = [rectangle_reset iterator;child] -> normal_statement child = true -> normal_statement body = true.
Proof. intros SHAPE NORMAL; apply flatten_normal_certificate; rewrite SHAPE; repeat constructor; exact NORMAL. Qed.

Lemma memory_frontend_positive_body fe ge locals iterator bound body written temps memory after final :
  normal_statement body = true -> writes_only written body -> ~ In iterator written -> ~ In bound written ->
  temps ! iterator = Some (Vint Int.zero) -> 0 < Int.signed (temp_word bound temps) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
  exists next target, exec_stmt fe ge locals temps memory body E0 next target Out_normal.
Proof.
  intros NORMAL WRITES ITERATOR BOUND ZERO POSITIVE SOURCE.
  destruct (frontend_entry_test SOURCE) as [flag TEST]; destruct (counter_test_domain TEST) as [word [upper [WORD LOOKUP]]].
  cbn [entry_temps] in WORD,LOOKUP.
  unfold temp_word in POSITIVE; rewrite LOOKUP in POSITIVE.
  assert (TRUE : expression_test (counter_condition iterator bound) (Entry ge locals temps memory) true).
  { replace true with (0 <? Int.signed upper) by (apply Z.ltb_lt; exact POSITIVE).
    apply (@counter_condition_at ge locals temps memory iterator bound 0 (Int.signed upper)).
    - intro SAME; subst bound; rewrite ZERO in LOOKUP; inversion LOOKUP; subst upper; rewrite Int.signed_zero in POSITIVE; lia.
    - exact ZERO.
    - rewrite Int.repr_signed; exact LOOKUP.
    - change (-2147483648 <= 0 <= 2147483647); lia.
    - apply Int.signed_range. }
  destruct (@frontend_iteration_decode fe ge locals temps memory iterator bound body after final TRUE
    (@normal_statement_execution fe ge locals body NORMAL)
    ltac:(intros; eapply structured_temp_frame; [exact WRITES|cbn; intuition congruence|eassumption]) SOURCE)
    as [next [target [BODY REST]]].
  exists next,target; exact BODY.
Qed.

Theorem memory_triple_source_words fe ge locals row row_bound column column_bound depth depth_bound
  body middle_body outer_body temps memory after final :
  row <> column -> row <> depth -> row_bound <> column -> row_bound <> depth ->
  column <> depth -> column_bound <> depth -> column_bound <> column -> depth_bound <> column -> depth_bound <> depth ->
  quiet_statement body = true -> writes_only [] body ->
  flatten_region middle_body = [rectangle_reset depth;frontend_counted_loop depth depth_bound body] ->
  flatten_region outer_body = [rectangle_reset column;frontend_counted_loop column column_bound middle_body] ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row row_bound outer_body) E0 after final Out_normal ->
  register_domain row (Entry ge locals temps memory) /\ register_domain row_bound (Entry ge locals temps memory) /\
  (temps ! row = Some (Vint Int.zero) -> 0 < Int.signed (temp_word row_bound temps) ->
    register_domain column_bound (Entry ge locals temps memory) /\
    (0 < Int.signed (temp_word column_bound temps) -> register_domain depth_bound (Entry ge locals temps memory))).
Proof.
  intros RC RD NC ND CD MD MC LC LD QUIET WRITES MIDDLE OUTER SOURCE.
  assert (MQUIET : quiet_statement middle_body = true).
  { eapply memory_reset_child_quiet; [exact MIDDLE|apply memory_frontend_loop_quiet; exact QUIET]. }
  assert (ONORMAL : normal_statement outer_body = true).
  { eapply memory_reset_child_normal; [exact OUTER|].
    change (quiet_statement (frontend_counted_loop column column_bound middle_body) = true).
    apply memory_frontend_loop_quiet; exact MQUIET. }
  assert (MNORMAL : normal_statement middle_body = true).
  { eapply memory_reset_child_normal; [exact MIDDLE|].
    change (quiet_statement (frontend_counted_loop depth depth_bound body) = true).
    apply memory_frontend_loop_quiet; exact QUIET. }
  assert (MWRITES : writes_only [depth] middle_body).
  { eapply memory_reset_child_writes; [exact MIDDLE|cbn; auto|].
    apply memory_frontend_loop_writes; [cbn; auto|].
    eapply writes_only_weaken with (small := []); [cbn; tauto|exact WRITES]. }
  assert (OWRITES : writes_only [column;depth] outer_body).
  { eapply memory_reset_child_writes; [exact OUTER|cbn; auto|].
    apply memory_frontend_loop_writes; [cbn; auto|].
    eapply writes_only_weaken with (small := [depth]); [cbn; tauto|exact MWRITES]. }
  destruct (frontend_entry_test SOURCE) as [flag TEST]; destruct (counter_test_domain TEST) as [word [upper [WORD LOOKUP]]].
  split; [exists word; exact WORD|]; split; [exists upper; exact LOOKUP|].
  intros ZERO NPOS.
  destruct (@memory_frontend_positive_body fe ge locals row row_bound outer_body [column;depth] temps memory after final
    ONORMAL OWRITES ltac:(cbn; intuition congruence) ltac:(cbn; intuition congruence) ZERO NPOS SOURCE)
    as [middle [target BODY]].
  pose proof (@memory_reset_child_decode fe ge locals outer_body column
    (frontend_counted_loop column column_bound middle_body) temps memory middle target OUTER BODY) as COLUMN_RUN.
  destruct (frontend_entry_test COLUMN_RUN) as [column_flag COLUMN_TEST];
    destruct (counter_test_domain COLUMN_TEST) as [column_word [column_upper [COLUMN_WORD COLUMN_LOOKUP]]].
  cbn [entry_temps] in COLUMN_LOOKUP; rewrite PTree.gso in COLUMN_LOOKUP by congruence.
  split; [exists column_upper; exact COLUMN_LOOKUP|]; intro MPOS.
  destruct (@memory_frontend_positive_body fe ge locals column column_bound middle_body [depth]
    (PTree.set column (Vint Int.zero) temps) memory middle target MNORMAL MWRITES
    ltac:(cbn; intuition congruence) ltac:(cbn; intuition congruence) (PTree.gss _ _ _)
    ltac:(unfold temp_word; rewrite PTree.gso by congruence; exact MPOS) COLUMN_RUN) as [next [result MIDDLE_RUN]].
  pose proof (@memory_reset_child_decode fe ge locals middle_body depth
    (frontend_counted_loop depth depth_bound body) (PTree.set column (Vint Int.zero) temps) memory next result MIDDLE MIDDLE_RUN) as DEPTH_RUN.
  destruct (frontend_entry_test DEPTH_RUN) as [depth_flag DEPTH_TEST];
    destruct (counter_test_domain DEPTH_TEST) as [depth_word [depth_upper [DEPTH_WORD DEPTH_LOOKUP]]].
  cbn [entry_temps] in DEPTH_LOOKUP; rewrite !PTree.gso in DEPTH_LOOKUP by congruence.
  exists depth_upper; exact DEPTH_LOOKUP.
Qed.
Print Assumptions memory_triple_source_words.
