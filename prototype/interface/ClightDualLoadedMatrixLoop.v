From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightCountedLoop
  ClightCountedProtocol ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax ClightStraightLine
  ClightTempFrame ClightRegionProgress ClightMatrixStore ClightMatrixLoops CompCertStoreSchedule.
From GuardInterface Require Import ClightReadonlyRewrite ClightStrictLoopProgress ClightStrictIteration
  ClightLoadedBoundSyntax ClightLoadedMatrixGuard ClightStableLoadBody ClightQuietDeterminacy
  ClightReadonlyLoadedTreeSynthesis ClightDualLoadedMatrixPrefix ClightActiveLoopTransport.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition dual_matrix_values rows columns cache q qo r ro le memory :=
  le ! rows = Some (Vptr q qo) /\ le ! columns = Some (Vptr r ro) /\
  le ! cache = Some (Vint (Int.repr 2)) /\
  Mem.loadv Mint32 memory (Vptr q qo) = Some (Vint (Int.repr 2)) /\
  Mem.loadv Mint32 memory (Vptr r ro) = Some (Vint (Int.repr 2)).
Definition dual_matrix_outer_snapshot limit row rows columns cache q qo r ro le memory :=
  exists i, 0 <= i <= limit /\ le ! row = Some (Vint (Int.repr i)) /\
    dual_matrix_values rows columns cache q qo r ro le memory.
Definition dual_matrix_inner_snapshot limit row rows column columns cache q qo r ro i le memory :=
  le ! row = Some (Vint (Int.repr i)) /\ exists j, 0 <= j <= limit /\
    le ! column = Some (Vint (Int.repr j)) /\ dual_matrix_values rows columns cache q qo r ro le memory.

Lemma dual_matrix_values_set rows columns cache q qo r ro le memory id value :
  id <> rows -> id <> columns -> id <> cache -> dual_matrix_values rows columns cache q qo r ro le memory ->
  dual_matrix_values rows columns cache q qo r ro (PTree.set id value le) memory.
Proof.
  intros N M C [Q [R [CACHE [READ READ2]]]]; unfold dual_matrix_values;
    repeat rewrite PTree.gso by congruence; auto.
Qed.
Lemma dual_matrix_lt_two i : 0 <= i <= 2 -> Int.lt (Int.repr i) (Int.repr 2) = true -> 0 <= i <= 1.
Proof.
  intros RANGE LT; unfold Int.lt in LT; rewrite !Int.signed_repr in LT by
    (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  destruct (zlt i 2); [lia|discriminate].
Qed.
Lemma dual_matrix_increment_values fe ge locals iterator rows columns cache q qo r ro le memory trace after final outcome i :
  iterator <> rows -> iterator <> columns -> iterator <> cache -> 0 <= i <= 1 ->
  le ! iterator = Some (Vint (Int.repr i)) -> dual_matrix_values rows columns cache q qo r ro le memory ->
  exec_stmt fe ge locals le memory (Ssequence Sskip (counter_increment iterator)) trace after final outcome ->
  after = PTree.set iterator (Vint (Int.repr (i+1))) le /\ final = memory /\
    dual_matrix_values rows columns cache q qo r ro after final.
Proof.
  intros N M C RANGE I VALUES RUN.
  destruct (@strict_increment_execution_exact fe ge locals iterator le memory trace after final outcome
    ltac:(exists (Int.repr i); split; [exact I|rewrite Int.signed_repr;
      change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia]) RUN)
    as [_ [TEMPS [MEMORY _]]]; subst after final.
  rewrite (@counter_increment_small iterator le i I).
  split; [reflexivity|split; [reflexivity|apply dual_matrix_values_set; assumption]].
Qed.

Theorem dual_matrix_body_values fe ge locals array row rows column columns cache body block q qo r ro
  i j le memory trace after final outcome :
  flatten_region body = [matrix_store array row column] -> matrix_array_binding ge locals array block ->
  (forall point, 0 <= point <= 3 -> Vptr block (Ptrofs.repr (4*point)) <> Vptr q qo /\
    Vptr block (Ptrofs.repr (4*point)) <> Vptr r ro) ->
  0 <= i <= 1 -> 0 <= j <= 1 -> le ! row = Some (Vint (Int.repr i)) ->
  le ! column = Some (Vint (Int.repr j)) -> dual_matrix_values rows columns cache q qo r ro le memory ->
  exec_stmt fe ge locals le memory body trace after final outcome ->
  after = le /\ dual_matrix_values rows columns cache q qo r ro le final.
Proof.
  intros BODY ARRAY APART IR JR I J [Q [R [CACHE [READ READ2]]]] RUN.
  pose proof (@quiet_execution_silent fe ge locals le memory body trace after final outcome RUN
    (@matrix_body_quiet array row column body BODY)) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals body (@matrix_body_normal array row column body BODY)
    le memory E0 after final outcome RUN) as NORMAL; subst outcome.
  apply (flattened_singleton_execution BODY) in RUN.
  destruct (@matrix_store_inverse fe ge locals le memory array row column i j E0 after final Out_normal I J IR JR RUN)
    as [other [OTHER [_ [TEMPS [_ STORE]]]]]; subst after.
  assert (SAME : block = other) by (eapply matrix_array_binding_unique; eassumption); subst other.
  split; [reflexivity|unfold dual_matrix_values; split; [exact Q|split; [exact R|split; [exact CACHE|split]]]].
  - eapply mint32_load_survives_apart_store.
    + exact (@loaded_matrix_storev block (i*2+j) (i*10+j+1) memory final ltac:(lia) STORE).
    + exact READ.
    + exact (proj1 (APART (i*2+j) ltac:(lia))).
  - eapply mint32_load_survives_apart_store.
    + exact (@loaded_matrix_storev block (i*2+j) (i*10+j+1) memory final ltac:(lia) STORE).
    + exact READ2.
    + exact (proj2 (APART (i*2+j) ltac:(lia))).
Qed.

Print Assumptions dual_matrix_increment_values.
Print Assumptions dual_matrix_body_values.

Theorem dual_matrix_inner_cached fe ge locals array row rows column columns cache body block q qo r ro i
  le memory trace after final outcome :
  row <> column -> column <> rows -> column <> columns -> cache <> column ->
  flatten_region body = [matrix_store array row column] -> matrix_array_binding ge locals array block ->
  (forall point, 0 <= point <= 3 -> Vptr block (Ptrofs.repr (4*point)) <> Vptr q qo /\
    Vptr block (Ptrofs.repr (4*point)) <> Vptr r ro) -> 0 <= i <= 1 ->
  dual_matrix_inner_snapshot 2 row rows column columns cache q qo r ro i le memory ->
  exec_stmt fe ge locals le memory (loaded_bound_loop column columns body) trace after final outcome ->
  exec_stmt fe ge locals le memory (frontend_counted_loop column cache body) trace after final outcome /\
    dual_matrix_inner_snapshot 2 row rows column columns cache q qo r ro i after final.
Proof.
  intros RC CN CM CC BODY ARRAY APART IR INV SOURCE.
  eapply strict_active_loop_transport with
    (invariant := dual_matrix_inner_snapshot 2 row rows column columns cache q qo r ro i)
    (body_invariant := dual_matrix_inner_snapshot 1 row rows column columns cache q qo r ro i);
    [| | | |exact SOURCE|exact INV].
  - intros before mem flag [I [j [JR [J [Q [R [CACHE [READ READ2]]]]]]]] TEST.
    exact (@loaded_bound_cached_test ge locals before mem column columns cache (Int.repr 2) r ro flag R READ2 CACHE TEST).
  - intros before mem tr exit mem' out [I [j [JR [J VALUES]]]] ACTIVE RUN.
    destruct VALUES as [Q [R [CACHE [READ READ2]]]].
    assert (LT : Int.lt (Int.repr j) (Int.repr 2) = true) by
      (eapply readonly_test_determinate;
        [exact (@loaded_bound_test_eval ge locals before mem column columns (Int.repr j) (Int.repr 2) r ro J R READ2)|exact ACTIVE]).
    pose proof (dual_matrix_lt_two JR LT) as SMALL.
    assert (VALUES : dual_matrix_values rows columns cache q qo r ro before mem) by
      (unfold dual_matrix_values; auto).
    destruct (@dual_matrix_body_values fe ge locals array row rows column columns cache body block q qo r ro i j
      before mem tr exit mem' out BODY ARRAY APART IR SMALL I J VALUES RUN) as [TEMPS AFTER]; subst exit.
    split; [exact RUN|split; [exact I|exists j; auto]].
  - intros before mem [I [j [JR [J VALUES]]]]; split; [exact I|exists j; split; [lia|auto]].
  - intros before mem tr exit mem' out [I [j [JR [J VALUES]]]] RUN.
    destruct (@dual_matrix_increment_values fe ge locals column rows columns cache q qo r ro before mem tr exit mem' out j
      CN CM ltac:(congruence) JR J VALUES RUN) as [TEMPS [MEMORY AFTER]]; subst exit mem'.
    split; [rewrite PTree.gso by congruence; exact I|exists (j+1); split; [lia|split; [apply PTree.gss|exact AFTER]]].
Qed.
Print Assumptions dual_matrix_inner_cached.

Theorem dual_matrix_outer_cached fe ge locals array row rows column columns cache body outer block q qo r ro
  le memory trace after final outcome :
  row <> column -> row <> rows -> row <> columns -> column <> rows -> column <> columns ->
  cache <> row -> cache <> column ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body] ->
  matrix_array_binding ge locals array block ->
  (forall point, 0 <= point <= 3 -> Vptr block (Ptrofs.repr (4*point)) <> Vptr q qo /\
    Vptr block (Ptrofs.repr (4*point)) <> Vptr r ro) ->
  dual_matrix_outer_snapshot 2 row rows columns cache q qo r ro le memory ->
  exec_stmt fe ge locals le memory (dual_matrix_source row rows outer) trace after final outcome ->
  exec_stmt fe ge locals le memory
    (frontend_counted_loop row cache (Ssequence (matrix_reset column) (frontend_counted_loop column cache body)))
    trace after final outcome /\ dual_matrix_outer_snapshot 2 row rows columns cache q qo r ro after final.
Proof.
  intros RC RN RM CN CM CR CC BODY OUTER ARRAY APART INV SOURCE.
  eapply strict_active_loop_transport with
    (invariant := dual_matrix_outer_snapshot 2 row rows columns cache q qo r ro)
    (body_invariant := dual_matrix_outer_snapshot 1 row rows columns cache q qo r ro);
    [| | | |exact SOURCE|exact INV].
  - intros before mem flag [i [IR [I [Q [R [CACHE [READ READ2]]]]]]] TEST.
    exact (@loaded_bound_cached_test ge locals before mem row rows cache (Int.repr 2) q qo flag Q READ CACHE TEST).
  - intros before mem tr exit mem' out [i [IR [I VALUES]]] ACTIVE RUN.
    destruct VALUES as [Q [R [CACHE [READ READ2]]]].
    assert (LT : Int.lt (Int.repr i) (Int.repr 2) = true) by
      (eapply readonly_test_determinate;
        [exact (@loaded_bound_test_eval ge locals before mem row rows (Int.repr i) (Int.repr 2) q qo I Q READ)|exact ACTIVE]).
    pose proof (dual_matrix_lt_two IR LT) as SMALL.
    pose proof (@quiet_execution_silent fe ge locals before mem outer tr exit mem' out RUN
      (@dual_matrix_outer_quiet array row column columns body outer BODY OUTER)) as SILENT; subst tr.
    pose proof (@normal_statement_execution fe ge locals outer
      (@dual_matrix_outer_normal array row column columns body outer BODY OUTER) before mem E0 exit mem' out RUN)
      as NORMAL; subst out.
    apply (@flattened_pair_execution fe ge locals outer (matrix_reset column)
      (loaded_bound_loop column columns body) before mem exit mem' OUTER) in RUN.
    destruct (sequence_normal_decode RUN) as [reset [resetmem [RESET INNER]]].
    destruct (matrix_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset resetmem.
    assert (VALUES : dual_matrix_values rows columns cache q qo r ro before mem) by
      (unfold dual_matrix_values; auto).
    assert (INNER_INV : dual_matrix_inner_snapshot 2 row rows column columns cache q qo r ro i
      (PTree.set column (Vint Int.zero) before) mem).
    { split; [rewrite PTree.gso by congruence; exact I|exists 0; split; [lia|split; [apply PTree.gss|]]].
      apply dual_matrix_values_set; assumption || congruence. }
    destruct (@dual_matrix_inner_cached fe ge locals array row rows column columns cache body block q qo r ro i
      _ mem E0 exit mem' Out_normal RC CN CM CC BODY ARRAY APART SMALL INNER_INV INNER) as [TARGET AFTER].
    destruct AFTER as [ROW [j [JR [J VALUES_AFTER]]]].
    split.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RESET|exact TARGET].
    + exists i; split; [exact SMALL|auto].
  - intros before mem [i [IR FACTS]]; exists i; split; [lia|exact FACTS].
  - intros before mem tr exit mem' out [i [IR [I VALUES]]] RUN.
    destruct (@dual_matrix_increment_values fe ge locals row rows columns cache q qo r ro before mem tr exit mem' out i
      RN RM ltac:(congruence) IR I VALUES RUN) as [TEMPS [MEMORY AFTER]]; subst exit mem'.
    exists (i+1); split; [lia|split; [apply PTree.gss|exact AFTER]].
Qed.
Print Assumptions dual_matrix_outer_cached.
