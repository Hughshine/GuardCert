From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightRedundantSet
  ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol ClightFrontendRegion ClightZeroTrip
  ClightLoopSyntax ClightLoopExecution ClightStraightLine ClightTempFrame ClightRegionProgress
  CompCertStoreSchedule RectangularSchedule ClightRectangularStore ClightRectangularGuard
  ClightRectangularLoops ClightRectangularRegion.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictIteration ClightStrictLoopProgress
  ClightReadonlyCellSwap ClightStableLoadBody ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_rectangle_source row bound outer_body := loaded_bound_loop row bound outer_body.
Definition loaded_rectangle_candidate d array row bound column columns cache :=
  Ssequence (Sset cache (signed_load bound))
    (rectangle_interchanged row cache column columns (rect_store d array row column)).

Lemma loaded_rectangle_outer_quiet d array row column columns body outer_body :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  quiet_statement outer_body = true.
Proof.
  intros BODY OUTER; apply flatten_quiet_certificate; rewrite OUTER.
  constructor; [reflexivity|constructor; [|constructor]].
  cbn [frontend_counted_loop quiet_statement counter_increment];
    rewrite (@rect_body_quiet d array row column body BODY); reflexivity.
Qed.
Lemma loaded_rectangle_source_quiet d array row bound column columns body outer_body :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  quiet_statement (loaded_rectangle_source row bound outer_body) = true.
Proof.
  intros BODY OUTER; cbn [loaded_rectangle_source loaded_bound_loop strict_frontend_loop quiet_statement counter_increment].
  rewrite (@loaded_rectangle_outer_quiet d array row column columns body outer_body BODY OUTER); reflexivity.
Qed.
Lemma loaded_rectangle_writes d array row bound column columns body outer_body :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  writes_only [row;column] (loaded_rectangle_source row bound outer_body).
Proof.
  intros BODY OUTER; pose proof (@rectangle_outer_writes column columns body outer_body
    (@rect_body_writes d array row column body BODY) OUTER) as WRITES.
  unfold loaded_rectangle_source, loaded_bound_loop, strict_frontend_loop, counter_increment.
  repeat constructor; cbn; auto.
  eapply writes_only_weaken; [|exact WRITES]; cbn; tauto.
Qed.

Lemma loaded_rectangle_columns_domain fe ge locals le memory d array row bound column columns body outer_body after final :
  column <> columns -> flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  expression_test (loaded_bound_test row bound) (Entry ge locals le memory) true ->
  exec_stmt fe ge locals le memory (loaded_rectangle_source row bound outer_body) E0 after final Out_normal ->
  exists word, le ! columns = Some (Vint word).
Proof.
  intros CM BODY OUTER ACTIVE SOURCE.
  destruct (@strict_active_iteration fe ge locals row (loaded_bound_test row bound) outer_body le memory after final
    (@rectangle_outer_normal column columns body outer_body (@rect_body_quiet d array row column body BODY) OUTER)
    (@loaded_rectangle_outer_quiet d array row column columns body outer_body BODY OUTER) ACTIVE SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY_RUN REST]]]]].
  apply (@flattened_pair_execution fe ge locals outer_body (rectangle_reset column)
    (frontend_counted_loop column columns body) le memory body_temps body_memory OUTER) in BODY_RUN.
  destruct (sequence_normal_decode BODY_RUN) as [reset_temps [reset_memory [RESET INNER]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset_temps reset_memory.
  destruct (frontend_entry_test INNER) as [flag TEST].
  destruct (@counter_test_domain column columns _ flag TEST) as [i [m [ITER COLS]]].
  exists m; cbn in COLS; rewrite PTree.gso in COLS by congruence; exact COLS.
Qed.

(** Decode an actual row without any non-alias or load-stability premise.
    Only already checked numeric layout bounds are used. *)
Theorem loaded_rectangle_row_decode d (VALID : rectangle_layout_valid d) fe ge locals
  array row bound column columns body outer_body N M i le memory after final :
  row <> bound -> row <> column -> bound <> column -> row <> columns -> column <> columns ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  0 < N <= rectangle_outer_limit d -> 0 < M <= rectangle_stride d -> 0 <= i < N ->
  le ! row = Some (Vint (Int.repr i)) -> le ! columns = Some (Vint (Int.repr M)) ->
  exec_stmt fe ge locals le memory outer_body E0 after final Out_normal ->
  counted_iterations (rect_point d ge locals array i) (Z.to_nat M) 0 memory final /\
    after = PTree.set column (Vint (Int.repr M)) le.
Proof.
  intros RQ RC QC RM CM BODY OUTER NR MR IR ROW COLS RUN.
  assert (NZ : Z.of_nat (Z.to_nat N) = N) by (apply Z2Nat.id; lia).
  assert (MZ : Z.of_nat (Z.to_nat M) = M) by (apply Z2Nat.id; lia).
  assert (MS : signed_range (Z.of_nat (Z.to_nat M))).
  { rewrite MZ; unfold signed_range, rectangle_layout_valid in *;
      change Int.min_signed with (-2147483648); lia. }
  assert (DECODE : forall x y temps before exit mem',
    0 <= x < Z.of_nat (Z.to_nat N) -> 0 <= y < Z.of_nat (Z.to_nat M) ->
    temps ! row = Some (Vint (Int.repr x)) -> temps ! column = Some (Vint (Int.repr y)) ->
    exec_stmt fe ge locals temps before body E0 exit mem' Out_normal ->
    rect_point d ge locals array x y before mem' /\ exit = temps).
  { intros x y temps before exit mem' X Y ROW' COL' STORE.
    apply (flattened_singleton_execution BODY) in STORE.
    destruct (@rect_store_inverse d VALID fe ge locals temps before array row column x y E0 exit mem' Out_normal
      ROW' COL' ltac:(apply rectangle_point_bound with (N := N) (M := M); auto; rewrite ?NZ, ?MZ in *; lia) STORE)
      as [block [ARRAY [_ [EXIT [_ WRITE]]]]].
    split; [exists block; split; [exact ARRAY|exact WRITE]|exact EXIT]. }
  pose proof (@rectangle_row_decode fe ge locals row bound column columns body outer_body (rect_point d ge locals array)
    (Z.to_nat N) (Z.to_nat M) RQ RC QC RM CM ltac:(intro ZERO; rewrite ZERO in NZ; cbn in NZ; lia)
    MS (@rect_body_normal d array row column body BODY) (@rect_body_writes d array row column body BODY)
    OUTER DECODE i le memory after final ltac:(rewrite NZ; exact IR) ROW ltac:(rewrite MZ; exact COLS) RUN) as ROW_RUN.
  rewrite MZ in ROW_RUN; exact ROW_RUN.
Qed.

Theorem loaded_rectangle_row_step d (VALID : rectangle_layout_valid d) fe ge locals le memory
  array row bound column columns body outer_body after final i upper M q qofs :
  row <> bound -> row <> column -> bound <> column -> row <> columns -> column <> columns ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  0 < Int.signed upper <= rectangle_outer_limit d -> 0 < M <= rectangle_stride d -> 0 <= i < Int.signed upper ->
  le ! row = Some (Vint (Int.repr i)) -> le ! bound = Some (Vptr q qofs) ->
  Mem.loadv Mint32 memory (Vptr q qofs) = Some (Vint upper) -> le ! columns = Some (Vint (Int.repr M)) ->
  exec_stmt fe ge locals le memory (loaded_rectangle_source row bound outer_body) E0 after final Out_normal ->
  exists row_memory,
    counted_iterations (rect_point d ge locals array i) (Z.to_nat M) 0 memory row_memory /\
    exec_stmt fe ge locals
      (PTree.set row (Vint (Int.repr (i+1))) (PTree.set column (Vint (Int.repr M)) le)) row_memory
      (loaded_rectangle_source row bound outer_body) E0 after final Out_normal.
Proof.
  intros RQ RC QC RM CM BODY OUTER NR MR IR ROW BOUND READ COLS SOURCE.
  assert (RANGE : signed_range i).
  { pose proof (Int.signed_range upper); unfold signed_range; change Int.min_signed with (-2147483648); lia. }
  assert (LT : Int.lt (Int.repr i) upper = true).
  { unfold Int.lt; rewrite Int.signed_repr by exact RANGE; destruct (zlt i (Int.signed upper)); [reflexivity|lia]. }
  assert (ACTIVE : expression_test (loaded_bound_test row bound) (Entry ge locals le memory) true).
  { rewrite <- LT; eapply loaded_bound_test_eval; eassumption. }
  destruct (@strict_active_iteration fe ge locals row (loaded_bound_test row bound) outer_body le memory after final
    (@rectangle_outer_normal column columns body outer_body (@rect_body_quiet d array row column body BODY) OUTER)
    (@loaded_rectangle_outer_quiet d array row column columns body outer_body BODY OUTER) ACTIVE SOURCE)
    as [body_temps [row_memory [next_temps [next_memory [ROW_RUN [INC TAIL]]]]]].
  destruct (@loaded_rectangle_row_decode d VALID fe ge locals array row bound column columns body outer_body
    (Int.signed upper) M i le memory body_temps row_memory RQ RC QC RM CM BODY OUTER NR MR IR ROW COLS ROW_RUN)
    as [POINTS TEMPS]; subst body_temps.
  assert (NEXT_ROW : (PTree.set column (Vint (Int.repr M)) le) ! row = Some (Vint (Int.repr i)))
    by (rewrite PTree.gso by congruence; exact ROW).
  destruct (@strict_increment_execution_exact fe ge locals row _ row_memory E0 next_temps next_memory Out_normal
    ltac:(exists (Int.repr i); split; [exact NEXT_ROW|rewrite Int.signed_repr by exact RANGE;
      pose proof (Int.signed_range upper); lia]) INC) as [_ [NEXT [MEMORY _]]]; subst next_temps next_memory.
  unfold increment_temps in TAIL; rewrite NEXT_ROW, Int.add_signed in TAIL.
  rewrite Int.signed_repr in TAIL by exact RANGE; change (Int.signed Int.one) with 1 in TAIL.
  exists row_memory; split; assumption.
Qed.

Print Assumptions loaded_rectangle_columns_domain.
Print Assumptions loaded_rectangle_row_decode.
Print Assumptions loaded_rectangle_row_step.
