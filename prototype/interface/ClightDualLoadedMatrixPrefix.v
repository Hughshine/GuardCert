From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightRedundantSet ClightNoWrap ClightPureExpr
  ClightCountedLoop ClightCountedProtocol ClightFrontendRegion ClightStraightLine ClightLoopExecution
  ClightLoopSyntax ClightTempFrame ClightRegionProgress ClightMatrixStore ClightMatrixLoops CompCertStoreSchedule.
From GuardInterface Require Import ClightReadonlyRewrite ClightStrictLoopProgress ClightStrictIteration
  ClightLoadedBoundSyntax ClightLoadedBoundGuard ClightLoadedMatrixSyntax ClightLoadedMatrixGuard
  ClightStableLoopCondition ClightDualLoadedUnitSyntax ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition dual_matrix_source row rows outer := loaded_bound_loop row rows outer.
Definition dual_matrix_candidate array row rows column cache :=
  Ssequence (Sset cache (signed_load rows)) (matrix_interchanged row cache column cache array).
Lemma dual_matrix_outer_quiet array row column columns body outer :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body] -> quiet_statement outer = true.
Proof.
  intros BODY OUTER; apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
  cbn [loaded_bound_loop strict_frontend_loop quiet_statement counter_increment];
    rewrite (@matrix_body_quiet array row column body BODY); reflexivity.
Qed.
Lemma dual_matrix_outer_normal array row column columns body outer :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body] -> normal_statement outer = true.
Proof.
  intros BODY OUTER; apply flatten_normal_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
  cbn [loaded_bound_loop strict_frontend_loop normal_statement quiet_statement counter_increment];
    rewrite (@matrix_body_quiet array row column body BODY); reflexivity.
Qed.
Lemma dual_matrix_source_quiet array row rows column columns body outer :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body] ->
  quiet_statement (dual_matrix_source row rows outer) = true.
Proof.
  intros BODY OUTER; cbn [dual_matrix_source loaded_bound_loop strict_frontend_loop quiet_statement counter_increment];
    rewrite (@dual_matrix_outer_quiet array row column columns body outer BODY OUTER); reflexivity.
Qed.
Lemma dual_matrix_source_writes array row rows column columns body outer :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body] ->
  writes_only [row;column] (dual_matrix_source row rows outer).
Proof.
  intros BODY OUTER.
  assert (BW : writes_only [row;column] body).
  { eapply writes_only_weaken; [|exact (@matrix_body_writes array row column body BODY)].
    intros id BAD; contradiction. }
  unfold dual_matrix_source, loaded_bound_loop, strict_frontend_loop, counter_increment; constructor.
  - constructor; [repeat constructor|].
    apply flatten_writes_certificate; rewrite OUTER; constructor; [constructor; cbn; auto|constructor; [|constructor]].
    unfold loaded_bound_loop, strict_frontend_loop, counter_increment; constructor.
    + constructor; [repeat constructor|exact BW].
    + constructor; [constructor|constructor; cbn; auto].
  - constructor; [constructor|constructor; cbn; auto].
Qed.

(** Open a real row, keeping its actual completion and outer continuation.
    In particular, the loaded inner bound has not been frozen yet. *)
Theorem dual_matrix_open_row fe ge locals le memory array row rows column columns body outer i q qo after final :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer = [matrix_reset column; loaded_bound_loop column columns body] ->
  0 <= i <= 1 -> le ! row = Some (Vint (Int.repr i)) -> le ! rows = Some (Vptr q qo) ->
  Mem.loadv Mint32 memory (Vptr q qo) = Some (Vint (Int.repr 2)) ->
  exec_stmt fe ge locals le memory (dual_matrix_source row rows outer) E0 after final Out_normal ->
  exists row_exit row_memory next next_memory,
    exec_stmt fe ge locals (PTree.set column (Vint Int.zero) le) memory
      (loaded_bound_loop column columns body) E0 row_exit row_memory Out_normal /\
    exec_stmt fe ge locals row_exit row_memory (Ssequence Sskip (counter_increment row)) E0 next next_memory Out_normal /\
    exec_stmt fe ge locals next next_memory (dual_matrix_source row rows outer) E0 after final Out_normal.
Proof.
  intros BODY OUTER RANGE I Q READ SOURCE.
  assert (ACTIVE : expression_test (loaded_bound_test row rows) (Entry ge locals le memory) true).
  { replace true with (Int.lt (Int.repr i) (Int.repr 2)).
    - eapply loaded_bound_test_eval; eassumption.
    - unfold Int.lt; rewrite !Int.signed_repr by
        (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
      destruct (zlt i 2); [reflexivity|lia]. }
  destruct (@strict_active_iteration fe ge locals row (loaded_bound_test row rows) outer le memory after final
    (@dual_matrix_outer_normal array row column columns body outer BODY OUTER)
    (@dual_matrix_outer_quiet array row column columns body outer BODY OUTER) ACTIVE SOURCE)
    as [row_exit [row_memory [next [next_memory [RUN [INC TAIL]]]]]].
  apply (@flattened_pair_execution fe ge locals outer (matrix_reset column)
    (loaded_bound_loop column columns body) le memory row_exit row_memory OUTER) in RUN.
  destruct (sequence_normal_decode RUN) as [reset [reset_memory [RESET INNER]]].
  destruct (matrix_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  exists row_exit,row_memory,next,next_memory; repeat split; assumption.
Qed.

(** One actual store is decoded before checking its aliases. No claim about
    the rest of the row or about either loaded bound is needed here. *)
Theorem dual_matrix_inner_step fe ge locals le memory array row column columns body i j r ro after final :
  row <> column -> flatten_region body = [matrix_store array row column] ->
  0 <= i <= 1 -> 0 <= j <= 1 ->
  le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
  le ! columns = Some (Vptr r ro) -> Mem.loadv Mint32 memory (Vptr r ro) = Some (Vint (Int.repr 2)) ->
  exec_stmt fe ge locals le memory (loaded_bound_loop column columns body) E0 after final Out_normal ->
  exists block middle, matrix_array_binding ge locals array block /\
    store_action_run (matrix_point block i j) memory middle /\
    exec_stmt fe ge locals (PTree.set column (Vint (Int.repr (j+1))) le) middle
      (loaded_bound_loop column columns body) E0 after final Out_normal.
Proof.
  intros RC BODY IR JR I J R READ SOURCE.
  assert (ACTIVE : expression_test (loaded_bound_test column columns) (Entry ge locals le memory) true).
  { replace true with (Int.lt (Int.repr j) (Int.repr 2)).
    - eapply loaded_bound_test_eval; eassumption.
    - unfold Int.lt; rewrite !Int.signed_repr by
        (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
      destruct (zlt j 2); [reflexivity|lia]. }
  destruct (@strict_active_iteration fe ge locals column (loaded_bound_test column columns) body le memory after final
    (@matrix_body_normal array row column body BODY) (@matrix_body_quiet array row column body BODY) ACTIVE SOURCE)
    as [body_exit [middle [next [next_memory [RUN [INC TAIL]]]]]].
  apply (flattened_singleton_execution BODY) in RUN.
  destruct (@matrix_store_inverse fe ge locals le memory array row column i j E0 body_exit middle Out_normal
    I J IR JR RUN) as [block [ARRAY [_ [TEMPS [_ STORE]]]]]; subst body_exit.
  destruct (@strict_increment_execution_exact fe ge locals column le middle E0 next next_memory Out_normal
    ltac:(exists (Int.repr j); split; [exact J|rewrite Int.signed_repr;
      change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia]) INC)
    as [_ [NEXT [MEMORY _]]]; subst next next_memory.
  unfold increment_temps in TAIL; rewrite J, Int.add_signed in TAIL.
  rewrite Int.signed_repr in TAIL by
    (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  change (Int.signed Int.one) with 1 in TAIL.
  exists block,middle; repeat split; assumption.
Qed.

Theorem dual_matrix_close_row fe ge locals le memory row rows column columns body outer i r ro row_exit row_memory next next_memory after final :
  0 <= i <= 1 -> le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr 2)) ->
  le ! columns = Some (Vptr r ro) -> Mem.loadv Mint32 memory (Vptr r ro) = Some (Vint (Int.repr 2)) ->
  quiet_statement body = true ->
  exec_stmt fe ge locals le memory (loaded_bound_loop column columns body) E0 row_exit row_memory Out_normal ->
  exec_stmt fe ge locals row_exit row_memory (Ssequence Sskip (counter_increment row)) E0 next next_memory Out_normal ->
  exec_stmt fe ge locals next next_memory (dual_matrix_source row rows outer) E0 after final Out_normal ->
  exec_stmt fe ge locals (PTree.set row (Vint (Int.repr (i+1))) le) memory
    (dual_matrix_source row rows outer) E0 after final Out_normal.
Proof.
  intros RANGE I J R READ QUIET INNER INC TAIL.
  assert (STOP : exec_stmt fe ge locals le memory (loaded_bound_loop column columns body) E0 le memory Out_normal).
  { apply strict_zero_trip_encode; change false with (Int.lt (Int.repr 2) (Int.repr 2));
      eapply loaded_bound_test_eval; eassumption. }
  assert (LOOP_QUIET : quiet_statement (loaded_bound_loop column columns body) = true).
  { cbn [loaded_bound_loop strict_frontend_loop quiet_statement counter_increment]; rewrite QUIET; reflexivity. }
  destruct (@quiet_execution_determinate fe ge locals le memory (loaded_bound_loop column columns body)
    E0 row_exit row_memory Out_normal INNER LOOP_QUIET E0 le memory Out_normal STOP)
    as [_ [TEMPS [MEMORY _]]]; subst row_exit row_memory.
  destruct (@strict_increment_execution_exact fe ge locals row le memory E0 next next_memory Out_normal
    ltac:(exists (Int.repr i); split; [exact I|rewrite Int.signed_repr;
      change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia]) INC)
    as [_ [TEMPS [MEMORY _]]]; subst next next_memory.
  unfold increment_temps in TAIL; rewrite I, Int.add_signed in TAIL.
  rewrite Int.signed_repr in TAIL by
    (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  change (Int.signed Int.one) with 1 in TAIL; exact TAIL.
Qed.

Print Assumptions dual_matrix_source_writes.
Print Assumptions dual_matrix_open_row.
Print Assumptions dual_matrix_inner_step.
Print Assumptions dual_matrix_close_row.
