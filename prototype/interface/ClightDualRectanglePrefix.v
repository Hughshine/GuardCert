From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightFrontendRegion ClightStraightLine ClightLoopExecution ClightLoopSyntax
  ClightTempFrame ClightRegionProgress ClightRectangularStore ClightRectangularGuard ClightRectangularLoops
  ClightRectangularRegion CompCertStoreSchedule RectangularSchedule.
From GuardInterface Require Import ClightReadonlyRewrite ClightStrictLoopProgress ClightStrictIteration
  ClightLoadedBoundSyntax ClightLoadedBoundGuard ClightReadonlyLoadedTreeSynthesis
  ClightLoadedRectangleMemory ClightQuietDeterminacy ClightDualLoadedUnitSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition dual_rect_source row rows outer := loaded_bound_loop row rows outer.
Definition dual_rect_candidate d array row rows column columns row_cache column_cache :=
  Ssequence (Sset row_cache (signed_load rows))
    (Ssequence (Sset column_cache (signed_load columns))
      (rectangle_interchanged row row_cache column column_cache (rect_store d array row column))).

Lemma dual_rect_outer_quiet d array row column columns body outer :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body] -> quiet_statement outer = true.
Proof.
  intros BODY OUTER; apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
  cbn [loaded_bound_loop strict_frontend_loop quiet_statement counter_increment];
    rewrite (@rect_body_quiet d array row column body BODY); reflexivity.
Qed.
Lemma dual_rect_outer_normal d array row column columns body outer :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body] -> normal_statement outer = true.
Proof.
  intros BODY OUTER; apply flatten_normal_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
  cbn [loaded_bound_loop strict_frontend_loop normal_statement quiet_statement counter_increment];
    rewrite (@rect_body_quiet d array row column body BODY); reflexivity.
Qed.
Lemma dual_rect_source_quiet d array row rows column columns body outer :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body] ->
  quiet_statement (dual_rect_source row rows outer) = true.
Proof.
  intros BODY OUTER; cbn [dual_rect_source loaded_bound_loop strict_frontend_loop quiet_statement counter_increment];
    rewrite (@dual_rect_outer_quiet d array row column columns body outer BODY OUTER); reflexivity.
Qed.
Lemma dual_rect_source_writes d array row rows column columns body outer :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body] ->
  writes_only [row;column] (dual_rect_source row rows outer).
Proof.
  intros BODY OUTER.
  assert (BW : writes_only [row;column] body).
  { eapply writes_only_weaken; [|exact (@rect_body_writes d array row column body BODY)].
    intros id BAD; contradiction. }
  unfold dual_rect_source, loaded_bound_loop, strict_frontend_loop, counter_increment; constructor.
  - constructor; [repeat constructor|].
    apply flatten_writes_certificate; rewrite OUTER; constructor; [constructor; cbn; auto|constructor; [|constructor]].
    unfold loaded_bound_loop, strict_frontend_loop, counter_increment; constructor.
    + constructor; [repeat constructor|exact BW].
    + constructor; [constructor|constructor; cbn; auto].
  - constructor; [constructor|constructor; cbn; auto].
Qed.

(** Actual inner completion and outer continuation remain separate. Neither
    bound is presumed stable before the current store passes both probes. *)
Theorem dual_rect_open_row fe ge locals le memory d array row rows column columns body outer i upper q qo after final :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body] ->
  0 <= i < Int.signed upper -> le ! row = Some (Vint (Int.repr i)) -> le ! rows = Some (Vptr q qo) ->
  Mem.loadv Mint32 memory (Vptr q qo) = Some (Vint upper) ->
  exec_stmt fe ge locals le memory (dual_rect_source row rows outer) E0 after final Out_normal ->
  exists row_exit row_memory next next_memory,
    exec_stmt fe ge locals (PTree.set column (Vint Int.zero) le) memory
      (loaded_bound_loop column columns body) E0 row_exit row_memory Out_normal /\
    exec_stmt fe ge locals row_exit row_memory (Ssequence Sskip (counter_increment row)) E0 next next_memory Out_normal /\
    exec_stmt fe ge locals next next_memory (dual_rect_source row rows outer) E0 after final Out_normal.
Proof.
  intros BODY OUTER RANGE I Q READ SOURCE.
  assert (ACTIVE : expression_test (loaded_bound_test row rows) (Entry ge locals le memory) true).
  { replace true with (Int.lt (Int.repr i) upper).
    - eapply loaded_bound_test_eval; eassumption.
    - unfold Int.lt; rewrite Int.signed_repr by
        (pose proof (Int.signed_range upper); change Int.min_signed with (-2147483648); lia).
      destruct (zlt i (Int.signed upper)); [reflexivity|lia]. }
  destruct (@strict_active_iteration fe ge locals row (loaded_bound_test row rows) outer le memory after final
    (@dual_rect_outer_normal d array row column columns body outer BODY OUTER)
    (@dual_rect_outer_quiet d array row column columns body outer BODY OUTER) ACTIVE SOURCE)
    as [row_exit [row_memory [next [next_memory [RUN [INC TAIL]]]]]].
  apply (@flattened_pair_execution fe ge locals outer (rectangle_reset column)
    (loaded_bound_loop column columns body) le memory row_exit row_memory OUTER) in RUN.
  destruct (sequence_normal_decode RUN) as [reset [reset_memory [RESET INNER]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  exists row_exit,row_memory,next,next_memory; repeat split; assumption.
Qed.

Theorem dual_rect_inner_step d (VALID : rectangle_layout_valid d) fe ge locals le memory
  array row column columns body i j width r ro after final :
  row <> column -> flatten_region body = [rect_store d array row column] ->
  0 <= i < rectangle_outer_limit d -> 0 < Int.signed width <= rectangle_stride d -> 0 <= j < Int.signed width ->
  le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
  le ! columns = Some (Vptr r ro) -> Mem.loadv Mint32 memory (Vptr r ro) = Some (Vint width) ->
  exec_stmt fe ge locals le memory (loaded_bound_loop column columns body) E0 after final Out_normal ->
  exists block middle, rect_array_binding d ge locals array block /\
    store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j)) memory middle /\
    exec_stmt fe ge locals (PTree.set column (Vint (Int.repr (j+1))) le) middle
      (loaded_bound_loop column columns body) E0 after final Out_normal.
Proof.
  intros RC BODY IR WR JR I J R READ SOURCE.
  assert (ACTIVE : expression_test (loaded_bound_test column columns) (Entry ge locals le memory) true).
  { replace true with (Int.lt (Int.repr j) width).
    - eapply loaded_bound_test_eval; eassumption.
    - unfold Int.lt; rewrite Int.signed_repr by
        (pose proof (Int.signed_range width); change Int.min_signed with (-2147483648); lia).
      destruct (zlt j (Int.signed width)); [reflexivity|lia]. }
  destruct (@strict_active_iteration fe ge locals column (loaded_bound_test column columns) body le memory after final
    (@rect_body_normal d array row column body BODY) (@rect_body_quiet d array row column body BODY) ACTIVE SOURCE)
    as [body_exit [middle [next [next_memory [RUN [INC TAIL]]]]]].
  apply (flattened_singleton_execution BODY) in RUN.
  assert (INDEX : 0 <= i*rectangle_stride d+j < rectangle_extent d).
  { eapply rectangle_point_bound; [exact VALID| |exact WR|exact IR|exact JR].
    pose proof (rectangle_limits VALID); lia. }
  destruct (@rect_store_inverse d VALID fe ge locals le memory array row column i j E0 body_exit middle Out_normal
    I J INDEX RUN) as [block [ARRAY [_ [TEMPS [_ STORE]]]]]; subst body_exit.
  destruct (@strict_increment_execution_exact fe ge locals column le middle E0 next next_memory Out_normal
    ltac:(exists (Int.repr j); split; [exact J|rewrite Int.signed_repr;
      pose proof (Int.signed_range width); change Int.min_signed with (-2147483648); lia]) INC)
    as [_ [NEXT [MEMORY _]]]; subst next next_memory.
  unfold increment_temps in TAIL; rewrite J, Int.add_signed in TAIL.
  rewrite Int.signed_repr in TAIL by
    (pose proof (Int.signed_range width); change Int.min_signed with (-2147483648); lia).
  change (Int.signed Int.one) with 1 in TAIL.
  exists block,middle; repeat split; assumption.
Qed.

Theorem dual_rect_close_row fe ge locals le memory row rows column columns body outer i upper width r ro
  row_exit row_memory next next_memory after final :
  0 <= i < Int.signed upper -> le ! row = Some (Vint (Int.repr i)) ->
  le ! column = Some (Vint width) -> le ! columns = Some (Vptr r ro) ->
  Mem.loadv Mint32 memory (Vptr r ro) = Some (Vint width) -> quiet_statement body = true ->
  exec_stmt fe ge locals le memory (loaded_bound_loop column columns body) E0 row_exit row_memory Out_normal ->
  exec_stmt fe ge locals row_exit row_memory (Ssequence Sskip (counter_increment row)) E0 next next_memory Out_normal ->
  exec_stmt fe ge locals next next_memory (dual_rect_source row rows outer) E0 after final Out_normal ->
  exec_stmt fe ge locals (PTree.set row (Vint (Int.repr (i+1))) le) memory
    (dual_rect_source row rows outer) E0 after final Out_normal.
Proof.
  intros RANGE I J R READ QUIET INNER INC TAIL.
  assert (STOP : exec_stmt fe ge locals le memory (loaded_bound_loop column columns body) E0 le memory Out_normal).
  { apply strict_zero_trip_encode; replace false with (Int.lt width width) by
      (unfold Int.lt; destruct (zlt (Int.signed width) (Int.signed width)); [lia|reflexivity]);
      eapply loaded_bound_test_eval; eassumption. }
  assert (LOOP_QUIET : quiet_statement (loaded_bound_loop column columns body) = true).
  { cbn [loaded_bound_loop strict_frontend_loop quiet_statement counter_increment]; rewrite QUIET; reflexivity. }
  destruct (@quiet_execution_determinate fe ge locals le memory (loaded_bound_loop column columns body)
    E0 row_exit row_memory Out_normal INNER LOOP_QUIET E0 le memory Out_normal STOP)
    as [_ [TEMPS [MEMORY _]]]; subst row_exit row_memory.
  destruct (@strict_increment_execution_exact fe ge locals row le memory E0 next next_memory Out_normal
    ltac:(exists (Int.repr i); split; [exact I|rewrite Int.signed_repr;
      pose proof (Int.signed_range upper); change Int.min_signed with (-2147483648); lia]) INC)
    as [_ [TEMPS [MEMORY _]]]; subst next next_memory.
  unfold increment_temps in TAIL; rewrite I, Int.add_signed in TAIL.
  rewrite Int.signed_repr in TAIL by
    (pose proof (Int.signed_range upper); change Int.min_signed with (-2147483648); lia).
  change (Int.signed Int.one) with 1 in TAIL; exact TAIL.
Qed.

Print Assumptions dual_rect_source_writes.
Print Assumptions dual_rect_open_row.
Print Assumptions dual_rect_inner_step.
Print Assumptions dual_rect_close_row.
