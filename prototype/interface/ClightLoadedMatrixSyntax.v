From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightRedundantSet ClightMatrixGuard ClightNoWrap ClightPureExpr ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightStraightLine ClightTempFrame ClightLoopSyntax
  ClightRegionProgress ClightSyntaxEquality ClightZeroTrip CompCertStoreSchedule ClightMatrixStore ClightMatrixLoops ClightStructuredProgress ClightFragmentProgress.
From GuardInterface Require Import ClightStrictLoopProgress ClightNestedStrictProgress ClightLoadedBoundSyntax
  ClightLoadedBoundCompiler ClightStableLoopCondition ClightStrictIteration ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_matrix_source row bound outer_body := loaded_bound_loop row bound outer_body.
Definition loaded_matrix_candidate row bound column columns array cache :=
  Ssequence (Sset cache (signed_load bound)) (matrix_interchanged row cache column columns array).
Definition loaded_nested_supported source :=
  match propose_loaded_bound source with
  | Some (iterator, bound, body) =>
    if statement_eq source (loaded_bound_loop iterator bound body)
      then structured_framed_supported (progress_syntax_size body) [iterator] body else false
  | None => false end.
Theorem loaded_nested_supported_sound source : loaded_nested_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold loaded_nested_supported; destruct (propose_loaded_bound source) as [[[iterator bound] body]|]; try discriminate.
  destruct (statement_eq source (loaded_bound_loop iterator bound body)) as [SAME|]; try discriminate.
  intro BODY; destruct (structured_framed_supported_sound _ _ _ BODY) as [F _]; subst source.
  exists (@strict_nested_region_progress iterator (loaded_bound_test iterator bound)
    (fun ge locals le memory => @loaded_bound_test_strict ge locals le memory iterator bound) []
    (fun BAD => BAD) body F); exact I.
Qed.
Lemma loaded_matrix_source_quiet array row bound column columns body outer_body :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  quiet_statement (loaded_matrix_source row bound outer_body) = true.
Proof.
  intros BODY OUTER.
  assert (QUIET : quiet_statement outer_body = true).
  { apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
    cbn [frontend_counted_loop quiet_statement counter_increment]; rewrite (@matrix_body_quiet array row column body BODY); reflexivity. }
  cbn [loaded_matrix_source loaded_bound_loop strict_frontend_loop quiet_statement counter_increment]; rewrite QUIET; reflexivity.
Qed.
Lemma loaded_matrix_writes array row bound column columns body outer_body :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  writes_only [row;column] (loaded_matrix_source row bound outer_body).
Proof.
  intros BODY OUTER; unfold loaded_matrix_source, loaded_bound_loop, strict_frontend_loop, counter_increment; constructor.
  - constructor; [repeat constructor|].
    eapply writes_only_weaken; [|exact (@matrix_outer_body_writes array row column columns body outer_body BODY OUTER)]; cbn; tauto.
  - repeat constructor; cbn; auto.
Qed.
Lemma loaded_matrix_entry_test fe ge locals le memory row bound outer_body after final :
  exec_stmt fe ge locals le memory (loaded_matrix_source row bound outer_body) E0 after final Out_normal ->
  exists flag, expression_test (loaded_bound_test row bound) (Entry ge locals le memory) flag.
Proof.
  intro SOURCE; inversion SOURCE; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Ssequence (Ssequence Sskip _) _) _ _ _ _ |- _ =>
    destruct (strict_header_execution HEADER) as [flag [TEST BRANCH]]; exists flag; exact TEST end.
Qed.
Lemma loaded_matrix_columns_domain fe ge locals le memory array row bound column columns body outer_body after final :
  column <> columns ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  expression_test (loaded_bound_test row bound) (Entry ge locals le memory) true ->
  exec_stmt fe ge locals le memory (loaded_matrix_source row bound outer_body) E0 after final Out_normal ->
  register_domain columns (Entry ge locals le memory).
Proof.
  intros CM BODY OUTER ACTIVE SOURCE.
  assert (QUIET : quiet_statement outer_body = true).
  { apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
    cbn [frontend_counted_loop quiet_statement counter_increment]; rewrite (@matrix_body_quiet array row column body BODY); reflexivity. }
  destruct (@strict_active_iteration fe ge locals row (loaded_bound_test row bound) outer_body le memory after final
    (@matrix_outer_body_normal array row column columns body outer_body BODY OUTER) QUIET ACTIVE SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY_RUN REST]]]]].
  apply (@flattened_pair_execution fe ge locals outer_body (matrix_reset column) (frontend_counted_loop column columns body) le memory body_temps body_memory OUTER) in BODY_RUN.
  destruct (sequence_normal_decode BODY_RUN) as [reset_temps [reset_memory [RESET INNER]]].
  destruct (matrix_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset_temps reset_memory.
  destruct (frontend_entry_test INNER) as [flag TEST].
  destruct (@counter_test_domain column columns _ flag TEST) as [i [m [ITER COLS]]].
  exists m; cbn in COLS |- *; rewrite PTree.gso in COLS by congruence; exact COLS.
Qed.

(** Decode a real outer iteration into its two stores and source tail. The
    bound may alias either store; no stability premise is used here. *)
Theorem loaded_matrix_row_step fe ge locals le memory array row bound column columns body outer_body
  after final point q qofs : row <> column -> column <> columns ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  0 <= point <= 1 -> le ! row = Some (Vint (Int.repr point)) ->
  le ! bound = Some (Vptr q qofs) -> Mem.loadv Mint32 memory (Vptr q qofs) = Some (Vint (Int.repr 2)) ->
  le ! columns = Some (Vint (Int.repr 2)) ->
  exec_stmt fe ge locals le memory (loaded_matrix_source row bound outer_body) E0 after final Out_normal ->
  exists block middle row_memory,
    matrix_array_binding ge locals array block /\
    store_action_run (matrix_point block point 0) memory middle /\
    store_action_run (matrix_point block point 1) middle row_memory /\
    exec_stmt fe ge locals
      (PTree.set row (Vint (Int.repr (point+1))) (PTree.set column (Vint (Int.repr 2)) le)) row_memory
      (loaded_matrix_source row bound outer_body) E0 after final Out_normal.
Proof.
  intros RC CM BODY OUTER RANGE ROW BOUND READ COLS SOURCE.
  assert (ACTIVE : expression_test (loaded_bound_test row bound) (Entry ge locals le memory) true).
  { replace true with (Int.lt (Int.repr point) (Int.repr 2)).
    - eapply loaded_bound_test_eval; eassumption.
    - unfold Int.lt; rewrite !Int.signed_repr by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
      destruct (zlt point 2); [reflexivity|lia]. }
  assert (QUIET : quiet_statement outer_body = true).
  { apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
    cbn [frontend_counted_loop quiet_statement counter_increment]; rewrite (@matrix_body_quiet array row column body BODY); reflexivity. }
  destruct (@strict_active_iteration fe ge locals row (loaded_bound_test row bound) outer_body le memory after final
    (@matrix_outer_body_normal array row column columns body outer_body BODY OUTER) QUIET ACTIVE SOURCE)
    as [body_temps [row_memory [next_temps [next_memory [ROW_RUN [INC TAIL]]]]]].
  destruct (@matrix_row_body_decode fe ge locals le memory array row column columns body outer_body point
    body_temps row_memory RC CM BODY OUTER ROW COLS RANGE ROW_RUN)
    as [block [middle [ARRAY [FIRST [SECOND TEMPS]]]]]; subst body_temps.
  assert (NEXT_ROW : (PTree.set column (Vint (Int.repr 2)) le) ! row = Some (Vint (Int.repr point)))
    by (rewrite PTree.gso by congruence; exact ROW).
  destruct (@strict_increment_execution_exact fe ge locals row _ row_memory E0 next_temps next_memory Out_normal
    ltac:(exists (Int.repr point); split; [exact NEXT_ROW|rewrite Int.signed_repr; change Int.max_signed with 2147483647;
      change Int.min_signed with (-2147483648); lia]) INC) as [_ [NEXT [MEMORY _]]]; subst next_temps next_memory.
  unfold increment_temps in TAIL; rewrite NEXT_ROW, Int.add_signed in TAIL.
  rewrite Int.signed_repr in TAIL by (change (-2147483648 <= point <= 2147483647); lia).
  change (Int.signed Int.one) with 1 in TAIL.
  exists block, middle, row_memory; repeat split; assumption.
Qed.
Print Assumptions loaded_nested_supported_sound.
Print Assumptions loaded_matrix_columns_domain.
Print Assumptions loaded_matrix_row_step.
