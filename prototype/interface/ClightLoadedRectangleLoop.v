From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightCountedProtocol ClightLoopSyntax
  ClightRegionProgress ClightStraightLine ClightRectangularStore ClightRectangularGuard ClightRectangularRegion.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictIteration ClightStableLoopCondition
  ClightActiveLoopCondition ClightReadonlyLoadedTreeSynthesis ClightQuietDeterminacy
  ClightLoadedRectangleRow ClightLoadedRectangleMemory.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_rectangle_snapshot limit row bound columns cache q qofs upper M le memory :=
  exists i, 0 <= i <= limit /\ le ! row = Some (Vint (Int.repr i)) /\
    le ! bound = Some (Vptr q qofs) /\ le ! columns = Some (Vint (Int.repr M)) /\
    le ! cache = Some (Vint upper) /\ Mem.loadv Mint32 memory (Vptr q qofs) = Some (Vint upper).

Lemma loaded_rectangle_body_snapshot d (VALID : rectangle_layout_valid d) fe ge locals array row bound column columns cache
  body outer_body block q qofs upper M le memory trace after final outcome :
  row <> bound -> row <> column -> bound <> column -> row <> columns -> column <> columns -> cache <> column ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [ClightRectangularLoops.rectangle_reset column; ClightFrontendLoopProtocol.frontend_counted_loop column columns body] ->
  rect_array_binding d ge locals array block -> 0 < Int.signed upper <= rectangle_outer_limit d -> 0 < M <= rectangle_stride d ->
  (forall i j, 0 <= i < Int.signed upper -> 0 <= j < M -> Vptr block (loaded_rectangle_offset d i j) <> Vptr q qofs) ->
  loaded_rectangle_snapshot (Int.signed upper) row bound columns cache q qofs upper M le memory ->
  expression_test (loaded_bound_test row bound) (Entry ge locals le memory) true ->
  exec_stmt fe ge locals le memory outer_body trace after final outcome ->
  loaded_rectangle_snapshot (Int.signed upper-1) row bound columns cache q qofs upper M after final.
Proof.
  intros RQ RC QC RM CM CC BODY OUTER ARRAY NR MR APART
    [i [IR [ROW [BOUND [COLS [CACHE READ]]]]]] ACTIVE RUN.
  assert (LT : Int.lt (Int.repr i) upper = true).
  { eapply readonly_test_determinate; [eapply loaded_bound_test_eval; eassumption|exact ACTIVE]. }
  assert (SMALL : 0 <= i < Int.signed upper).
  { unfold Int.lt in LT; rewrite Int.signed_repr in LT by
      (pose proof (Int.signed_range upper); change Int.min_signed with (-2147483648); lia).
    destruct (zlt i (Int.signed upper)); cbn in LT; [lia|discriminate]. }
  pose proof (@quiet_execution_silent fe ge locals le memory outer_body trace after final outcome RUN
    (@loaded_rectangle_outer_quiet d array row column columns body outer_body BODY OUTER)) as SILENT.
  pose proof (@normal_statement_execution fe ge locals outer_body
    (@ClightRectangularLoops.rectangle_outer_normal column columns body outer_body
      (@rect_body_quiet d array row column body BODY) OUTER) le memory trace after final outcome RUN) as NORMAL.
  subst trace outcome.
  destruct (@loaded_rectangle_row_decode d VALID fe ge locals array row bound column columns body outer_body
    (Int.signed upper) M i le memory after final RQ RC QC RM CM BODY OUTER NR MR SMALL ROW COLS RUN)
    as [POINTS TEMPS]; subst after.
  assert (NEXT_READ : Mem.loadv Mint32 final (Vptr q qofs) = Some (Vint upper)).
  { exact (@loaded_rectangle_row_load d VALID ge locals array block i M (Z.to_nat M) 0 memory final q qofs (Vint upper)
      ARRAY ltac:(lia) MR ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) (fun j JR => APART i j SMALL JR) READ POINTS). }
  exists i; split; [lia|].
  repeat split; try (rewrite PTree.gso by congruence); assumption.
Qed.

Lemma loaded_rectangle_increment_snapshot fe ge locals row bound columns cache q qofs upper M le memory trace after final outcome :
  row <> bound -> row <> columns -> cache <> row ->
  loaded_rectangle_snapshot (Int.signed upper-1) row bound columns cache q qofs upper M le memory ->
  exec_stmt fe ge locals le memory (Ssequence Sskip (counter_increment row)) trace after final outcome ->
  loaded_rectangle_snapshot (Int.signed upper) row bound columns cache q qofs upper M after final.
Proof.
  intros RQ RM CR [i [IR [ROW [BOUND [COLS [CACHE READ]]]]]] RUN.
  assert (RANGE : signed_range i) by
    (pose proof (Int.signed_range upper); unfold signed_range; change Int.min_signed with (-2147483648); lia).
  destruct (@strict_increment_execution_exact fe ge locals row le memory trace after final outcome
    ltac:(exists (Int.repr i); split; [exact ROW|rewrite Int.signed_repr by exact RANGE; pose proof (Int.signed_range upper); lia]) RUN)
    as [_ [TEMPS [MEMORY _]]]; subst after final.
  unfold increment_temps; rewrite ROW, Int.add_signed, Int.signed_repr by exact RANGE.
  change (Int.signed Int.one) with 1; exists (i+1); split; [lia|].
  split; [apply PTree.gss|repeat split; try (rewrite PTree.gso by congruence); assumption].
Qed.

Theorem loaded_rectangle_cached d (VALID : rectangle_layout_valid d) fe ge locals array row bound column columns cache
  body outer_body block q qofs upper M le memory trace after final outcome :
  row <> bound -> row <> column -> bound <> column -> row <> columns -> column <> columns -> cache <> row -> cache <> column ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [ClightRectangularLoops.rectangle_reset column; ClightFrontendLoopProtocol.frontend_counted_loop column columns body] ->
  rect_array_binding d ge locals array block -> 0 < Int.signed upper <= rectangle_outer_limit d -> 0 < M <= rectangle_stride d ->
  (forall i j, 0 <= i < Int.signed upper -> 0 <= j < M -> Vptr block (loaded_rectangle_offset d i j) <> Vptr q qofs) ->
  loaded_rectangle_snapshot (Int.signed upper) row bound columns cache q qofs upper M le memory ->
  exec_stmt fe ge locals le memory (loaded_rectangle_source row bound outer_body) trace after final outcome ->
  exec_stmt fe ge locals le memory (ClightFrontendLoopProtocol.frontend_counted_loop row cache outer_body) trace after final outcome.
Proof.
  intros RQ RC QC RM CM CR CC BODY OUTER ARRAY NR MR APART INV SOURCE.
  exact (proj1 (@strict_active_condition_transport fe ge locals row (loaded_bound_test row bound) (counter_condition row cache) outer_body
    (loaded_rectangle_snapshot (Int.signed upper) row bound columns cache q qofs upper M)
    (loaded_rectangle_snapshot (Int.signed upper-1) row bound columns cache q qofs upper M)
    ltac:(intros before mem flag [i [IR [ROW [BOUND [COLS [CACHE READ]]]]]] TEST; eapply loaded_bound_cached_test; eassumption)
    (fun before mem tr exit mem' out' INV TEST RUN => @loaded_rectangle_body_snapshot d VALID fe ge locals array row bound column columns cache
      body outer_body block q qofs upper M before mem tr exit mem' out' RQ RC QC RM CM CC BODY OUTER ARRAY NR MR APART INV TEST RUN)
    ltac:(intros before mem [i [IR FACTS]]; exists i; split; [lia|exact FACTS])
    (fun before mem tr exit mem' out' INV RUN => @loaded_rectangle_increment_snapshot fe ge locals row bound columns cache q qofs upper M
      before mem tr exit mem' out' RQ RM CR INV RUN)
    le memory trace after final outcome SOURCE INV)).
Qed.

Print Assumptions loaded_rectangle_body_snapshot.
Print Assumptions loaded_rectangle_increment_snapshot.
Print Assumptions loaded_rectangle_cached.
