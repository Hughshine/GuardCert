From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol
  ClightLoopSyntax ClightLoopExecution ClightStraightLine ClightTempFrame ClightRegionProgress ClightRectangularStore ClightRectangularGuard
  ClightRectangularLoops ClightRectangularRegion RectangularSchedule CompCertStoreSchedule.
From GuardInterface Require Import ClightReadonlyRewrite ClightLoadedBoundSyntax ClightStableLoadBody ClightStrictIteration
  ClightStableLoopCondition ClightReadonlyLoadedTreeSynthesis ClightQuietDeterminacy ClightActiveLoopTransport
  ClightLoadedRectangleMemory ClightDualRectanglePrefix ClightDualLoadedUnitSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition dual_rect_values rows columns row_cache column_cache upper width q qo r ro le memory :=
  le ! rows = Some (Vptr q qo) /\ le ! columns = Some (Vptr r ro) /\
  le ! row_cache = Some (Vint upper) /\ le ! column_cache = Some (Vint width) /\
  Mem.loadv Mint32 memory (Vptr q qo) = Some (Vint upper) /\ Mem.loadv Mint32 memory (Vptr r ro) = Some (Vint width).
Definition dual_rect_outer_snapshot limit row rows columns row_cache column_cache upper width q qo r ro le memory :=
  exists i, 0 <= i <= limit /\ le ! row = Some (Vint (Int.repr i)) /\
    dual_rect_values rows columns row_cache column_cache upper width q qo r ro le memory.
Definition dual_rect_inner_snapshot limit row rows column columns row_cache column_cache upper width q qo r ro i le memory :=
  le ! row = Some (Vint (Int.repr i)) /\ exists j, 0 <= j <= limit /\ le ! column = Some (Vint (Int.repr j)) /\
    dual_rect_values rows columns row_cache column_cache upper width q qo r ro le memory.
Lemma dual_rect_values_set rows columns row_cache column_cache upper width q qo r ro le memory id value :
  id <> rows -> id <> columns -> id <> row_cache -> id <> column_cache ->
  dual_rect_values rows columns row_cache column_cache upper width q qo r ro le memory ->
  dual_rect_values rows columns row_cache column_cache upper width q qo r ro (PTree.set id value le) memory.
Proof.
  intros N M C K [Q [R [CACHE [CACHE2 [READ READ2]]]]]; unfold dual_rect_values; repeat rewrite PTree.gso by congruence; repeat split; assumption.
Qed.
Lemma dual_rect_active_range i upper : 0 <= i <= Int.signed upper -> Int.lt (Int.repr i) upper = true -> 0 <= i < Int.signed upper.
Proof.
  intros RANGE LT; unfold Int.lt in LT; rewrite Int.signed_repr in LT by
    (pose proof (Int.signed_range upper); change Int.min_signed with (-2147483648); lia).
  destruct (zlt i (Int.signed upper)); [lia|discriminate].
Qed.
Lemma dual_rect_increment_values fe ge locals iterator rows columns row_cache column_cache upper width q qo r ro
  le memory trace after final outcome i :
  iterator <> rows -> iterator <> columns -> iterator <> row_cache -> iterator <> column_cache ->
  0 <= i < Int.max_signed -> le ! iterator = Some (Vint (Int.repr i)) ->
  dual_rect_values rows columns row_cache column_cache upper width q qo r ro le memory ->
  exec_stmt fe ge locals le memory (Ssequence Sskip (counter_increment iterator)) trace after final outcome ->
  after = PTree.set iterator (Vint (Int.repr (i+1))) le /\ final = memory /\
    dual_rect_values rows columns row_cache column_cache upper width q qo r ro after final.
Proof.
  intros N M C K RANGE I VALUES RUN.
  destruct (@strict_increment_execution_exact fe ge locals iterator le memory trace after final outcome
    ltac:(exists (Int.repr i); split; [exact I|rewrite Int.signed_repr; change Int.min_signed with (-2147483648); lia]) RUN)
    as [_ [TEMPS [MEMORY _]]]; subst after final; rewrite (@counter_increment_small iterator le i I).
  split; [reflexivity|split; [reflexivity|apply dual_rect_values_set; assumption]].
Qed.

Section CACHED.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables ge : genv.
Variable locals : env.
Variables array row rows column columns row_cache column_cache : ident.
Variables body outer : statement.
Variables block q r : block.
Variables qo ro : ptrofs.
Variables upper width : int.
Hypotheses (RC : row <> column) (RN : row <> rows) (RM : row <> columns) (CN : column <> rows) (CM : column <> columns)
  (CR : row_cache <> row) (CC : row_cache <> column) (KR : column_cache <> row) (KC : column_cache <> column).
Hypotheses (BODY : flatten_region body = [rect_store d array row column])
  (OUTER : flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body])
  (ARRAY : rect_array_binding d ge locals array block)
  (NR : 0 < Int.signed upper <= rectangle_outer_limit d) (MR : 0 < Int.signed width <= rectangle_stride d)
  (APART : forall i j, 0 <= i < Int.signed upper -> 0 <= j < Int.signed width ->
    Vptr block (loaded_rectangle_offset d i j) <> Vptr q qo /\ Vptr block (loaded_rectangle_offset d i j) <> Vptr r ro).

Lemma dual_rect_body_values i j le memory trace after final outcome :
  0 <= i < Int.signed upper -> 0 <= j < Int.signed width -> le ! row = Some (Vint (Int.repr i)) ->
  le ! column = Some (Vint (Int.repr j)) ->
  dual_rect_values rows columns row_cache column_cache upper width q qo r ro le memory ->
  exec_stmt fe ge locals le memory body trace after final outcome ->
  after = le /\ dual_rect_values rows columns row_cache column_cache upper width q qo r ro le final.
Proof.
  intros IR JR I J [Q [R [CACHE [CACHE2 [READ READ2]]]]] RUN.
  pose proof (@quiet_execution_silent fe ge locals le memory body trace after final outcome RUN (@rect_body_quiet d array row column body BODY)) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals body (@rect_body_normal d array row column body BODY)
    le memory E0 after final outcome RUN) as NORMAL; subst outcome.
  apply (flattened_singleton_execution BODY) in RUN.
  assert (INDEX : 0 <= i*rectangle_stride d+j < rectangle_extent d) by (eapply rectangle_point_bound; eassumption).
  destruct (@rect_store_inverse d VALID fe ge locals le memory array row column i j E0 after final Out_normal I J INDEX RUN)
    as [other [OTHER [_ [TEMPS [_ STORE]]]]]; subst after.
  assert (SAME : block = other) by (eapply rect_array_binding_unique; eassumption); subst other.
  split; [reflexivity|unfold dual_rect_values; repeat split; try assumption].
  - eapply mint32_load_survives_apart_store;
      [exact (@loaded_rectangle_storev d VALID block i j memory final INDEX STORE)|exact READ|exact (proj1 (APART IR JR))].
  - eapply mint32_load_survives_apart_store;
      [exact (@loaded_rectangle_storev d VALID block i j memory final INDEX STORE)|exact READ2|exact (proj2 (APART IR JR))].
Qed.

Theorem dual_rect_inner_cached i le memory trace after final outcome : 0 <= i < Int.signed upper ->
  dual_rect_inner_snapshot (Int.signed width) row rows column columns row_cache column_cache upper width q qo r ro i le memory ->
  exec_stmt fe ge locals le memory (loaded_bound_loop column columns body) trace after final outcome ->
  exec_stmt fe ge locals le memory (frontend_counted_loop column column_cache body) trace after final outcome /\
    dual_rect_inner_snapshot (Int.signed width) row rows column columns row_cache column_cache upper width q qo r ro i after final.
Proof.
  intros IR INV SOURCE.
  eapply strict_active_loop_transport with
    (invariant := dual_rect_inner_snapshot (Int.signed width) row rows column columns row_cache column_cache upper width q qo r ro i)
    (body_invariant := dual_rect_inner_snapshot (Int.signed width-1) row rows column columns row_cache column_cache upper width q qo r ro i);
    [| | | |exact SOURCE|exact INV].
  - intros before mem flag [I [j [JR [J [Q [R [CACHE [CACHE2 [READ READ2]]]]]]]]] TEST.
    exact (@loaded_bound_cached_test ge locals before mem column columns column_cache width r ro flag R READ2 CACHE2 TEST).
  - intros before mem tr exit mem' out [I [j [JR [J VALUES]]]] ACTIVE RUN.
    destruct VALUES as [Q [R [CACHE [CACHE2 [READ READ2]]]]].
    assert (LT : Int.lt (Int.repr j) width = true) by
      (eapply readonly_test_determinate;
        [exact (@loaded_bound_test_eval ge locals before mem column columns (Int.repr j) width r ro J R READ2)|exact ACTIVE]).
    pose proof (@dual_rect_active_range j width JR LT) as SMALL.
    assert (VALUES : dual_rect_values rows columns row_cache column_cache upper width q qo r ro before mem) by (unfold dual_rect_values; repeat split; assumption).
    destruct (dual_rect_body_values IR SMALL I J VALUES RUN) as [TEMPS AFTER]; subst exit.
    split; [exact RUN|split; [exact I|exists j; split; [lia|auto]]].
  - intros before mem [I [j [JR [J VALUES]]]]; split; [exact I|exists j; split; [lia|auto]].
  - intros before mem tr exit mem' out [I [j [JR [J VALUES]]]] RUN.
    destruct (@dual_rect_increment_values fe ge locals column rows columns row_cache column_cache upper width q qo r ro before mem tr exit mem' out j
      CN CM ltac:(congruence) ltac:(congruence) ltac:(pose proof (Int.signed_range width); lia) J VALUES RUN)
      as [TEMPS [MEMORY AFTER]]; subst exit mem'.
    split; [rewrite PTree.gso by congruence; exact I|exists (j+1); split; [lia|split; [apply PTree.gss|exact AFTER]]].
Qed.

Theorem dual_rect_outer_cached le memory trace after final outcome :
  dual_rect_outer_snapshot (Int.signed upper) row rows columns row_cache column_cache upper width q qo r ro le memory ->
  exec_stmt fe ge locals le memory (dual_rect_source row rows outer) trace after final outcome ->
  exec_stmt fe ge locals le memory
    (frontend_counted_loop row row_cache (Ssequence (rectangle_reset column) (frontend_counted_loop column column_cache body)))
    trace after final outcome /\
    dual_rect_outer_snapshot (Int.signed upper) row rows columns row_cache column_cache upper width q qo r ro after final.
Proof.
  intros INV SOURCE.
  eapply strict_active_loop_transport with
    (invariant := dual_rect_outer_snapshot (Int.signed upper) row rows columns row_cache column_cache upper width q qo r ro)
    (body_invariant := dual_rect_outer_snapshot (Int.signed upper-1) row rows columns row_cache column_cache upper width q qo r ro);
    [| | | |exact SOURCE|exact INV].
  - intros before mem flag [i [IR [I [Q [R [CACHE [CACHE2 [READ READ2]]]]]]]] TEST.
    exact (@loaded_bound_cached_test ge locals before mem row rows row_cache upper q qo flag Q READ CACHE TEST).
  - intros before mem tr exit mem' out [i [IR [I VALUES]]] ACTIVE RUN.
    destruct VALUES as [Q [R [CACHE [CACHE2 [READ READ2]]]]].
    assert (LT : Int.lt (Int.repr i) upper = true) by
      (eapply readonly_test_determinate;
        [exact (@loaded_bound_test_eval ge locals before mem row rows (Int.repr i) upper q qo I Q READ)|exact ACTIVE]).
    pose proof (@dual_rect_active_range i upper IR LT) as SMALL.
    pose proof (@quiet_execution_silent fe ge locals before mem outer tr exit mem' out RUN
      (@dual_rect_outer_quiet d array row column columns body outer BODY OUTER)) as SILENT; subst tr.
    pose proof (@normal_statement_execution fe ge locals outer (@dual_rect_outer_normal d array row column columns body outer BODY OUTER)
      before mem E0 exit mem' out RUN) as NORMAL; subst out.
    apply (@flattened_pair_execution fe ge locals outer (rectangle_reset column) (loaded_bound_loop column columns body)
      before mem exit mem' OUTER) in RUN.
    destruct (sequence_normal_decode RUN) as [reset [resetmem [RESET INNER]]].
    destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset resetmem.
    assert (VALUES : dual_rect_values rows columns row_cache column_cache upper width q qo r ro before mem) by (unfold dual_rect_values; repeat split; assumption).
    assert (INNER_INV : dual_rect_inner_snapshot (Int.signed width) row rows column columns row_cache column_cache upper width q qo r ro i
      (PTree.set column (Vint Int.zero) before) mem).
    { split; [rewrite PTree.gso by congruence; exact I|exists 0; split; [lia|split; [apply PTree.gss|]]].
      apply dual_rect_values_set; assumption || congruence. }
    destruct (dual_rect_inner_cached SMALL INNER_INV INNER) as [TARGET AFTER].
    destruct AFTER as [ROW [j [JR [J VALUES_AFTER]]]].
    split; [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RESET|exact TARGET]|exists i; split; [lia|auto]].
  - intros before mem [i [IR FACTS]]; exists i; split; [lia|exact FACTS].
  - intros before mem tr exit mem' out [i [IR [I VALUES]]] RUN.
    destruct (@dual_rect_increment_values fe ge locals row rows columns row_cache column_cache upper width q qo r ro before mem tr exit mem' out i
      RN RM ltac:(congruence) ltac:(congruence) ltac:(pose proof (Int.signed_range upper); lia) I VALUES RUN)
      as [TEMPS [MEMORY AFTER]]; subst exit mem'.
    exists (i+1); split; [lia|split; [apply PTree.gss|exact AFTER]].
Qed.
End CACHED.

Print Assumptions dual_rect_increment_values.
Print Assumptions dual_rect_body_values.
Print Assumptions dual_rect_inner_cached.
Print Assumptions dual_rect_outer_cached.
