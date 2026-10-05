From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import SemanticFacts ClightCondition ClightNoWrap ClightRedundantSet ClightMatrixGuard
  ClightRectangularGuard ClightRectangularStore ClightRectangularLoops ClightCountedLoop ClightCountedProtocol
  ClightFramedLoop ClightZeroTrip ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightStraightLine
  ClightLoopSyntax ClightTempFrame ClightRegionProgress.
From GuardInterface Require Import ClightRuntimeStrideBody ClightRuntimeStrideLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition runtime_stride_domain row bound inner_bound stride entry :=
  rectangle_guard_domain row bound inner_bound entry /\
  (register_equals row Int.zero tt entry -> 0 < Int.signed (temp_word bound (entry_temps entry)) ->
    0 < Int.signed (temp_word inner_bound (entry_temps entry)) -> register_domain stride entry).

Theorem runtime_stride_domain_from_source fe ge locals d array row bound column inner_bound stride body outer_body
  le memory after final :
  row <> bound -> row <> column -> bound <> column -> column <> inner_bound -> stride <> column ->
  flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body] ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  runtime_stride_domain row bound inner_bound stride (Entry ge locals le memory).
Proof.
  intros RN RC NC CM SC FLAT OUTER SOURCE.
  destruct (@frontend_entry_test fe ge locals le memory row bound outer_body after final SOURCE) as [flag TEST].
  destruct (@counter_test_domain row bound (Entry ge locals le memory) flag TEST) as [x [upper [I N]]].
  cbn [entry_temps] in I, N.
  assert (FIRST : forall ZERO : register_equals row Int.zero tt (Entry ge locals le memory),
    0 < Int.signed (temp_word bound le) -> exists body_temps body_mem,
    exec_stmt fe ge locals (PTree.set column (Vint Int.zero) le) memory
      (frontend_counted_loop column inner_bound body) E0 body_temps body_mem Out_normal).
  { intros ZERO POS.
    assert (ACTIVE : expression_test (counter_condition row bound) (Entry ge locals le memory) true).
    { unfold temp_word in POS; rewrite N in POS.
      replace true with (0 <? Int.signed upper) by (apply Z.ltb_lt; exact POS).
      apply (@counter_condition_at ge locals le memory row bound 0 (Int.signed upper));
        try exact RN; try apply Int.signed_range;
        try (change (-2147483648 <= 0 <= 2147483647); lia); try exact ZERO.
      rewrite Int.repr_signed; exact N. }
    assert (WRITES := @rectangle_outer_writes column inner_bound body outer_body
      (@runtime_body_writes d array row column stride body FLAT) OUTER).
    assert (FRAME : forall before mem tr exit mem', exec_stmt fe ge locals before mem outer_body tr exit mem' Out_normal ->
      temp_agree [row;bound] before exit).
    { intros; eapply structured_temp_frame; [exact WRITES|cbn; intros id IN BAD; intuition congruence|eassumption]. }
    destruct (@frontend_iteration_decode fe ge locals le memory row bound outer_body after final ACTIVE
      (@normal_statement_execution fe ge locals outer_body
        (@rectangle_outer_normal column inner_bound body outer_body (@runtime_body_quiet d array row column stride body FLAT) OUTER))
      FRAME SOURCE) as [middle [mem1 [BODY_RUN REST]]].
    apply (@flattened_pair_execution fe ge locals outer_body (rectangle_reset column)
      (frontend_counted_loop column inner_bound body) le memory middle mem1 OUTER) in BODY_RUN.
    destruct (sequence_normal_decode BODY_RUN) as [reset_temps [reset_mem [RESET INNER]]].
    destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset_temps reset_mem.
    do 2 eexists; exact INNER. }
  assert (INNER_DOMAIN : register_equals row Int.zero tt (Entry ge locals le memory) ->
    0 < Int.signed (temp_word bound le) -> register_domain inner_bound (Entry ge locals le memory)).
  { intros ZERO POS; destruct (FIRST ZERO POS) as [middle [mem1 INNER]].
    destruct (@frontend_entry_test fe ge locals _ memory column inner_bound body middle mem1 INNER) as [inner_flag INNER_TEST].
    destruct (@counter_test_domain column inner_bound _ inner_flag INNER_TEST) as [j [m [J M]]].
    exists m; cbn in M |- *; rewrite PTree.gso in M by congruence; exact M. }
  split.
  - split; [exists x; exact I|split; [exists upper; exact N|exact INNER_DOMAIN]].
  - intros ZERO POS M_POS.
    destruct (INNER_DOMAIN ZERO POS) as [m M]; cbn [entry_temps] in M.
    unfold temp_word in M_POS; cbn [entry_temps] in M_POS; rewrite M in M_POS.
    destruct (FIRST ZERO POS) as [middle [mem1 INNER]].
    assert (ACTIVE : expression_test (counter_condition column inner_bound)
      (Entry ge locals (PTree.set column (Vint Int.zero) le) memory) true).
    { replace true with (0 <? Int.signed m) by (apply Z.ltb_lt; exact M_POS).
      apply (@counter_condition_at ge locals _ memory column inner_bound 0 (Int.signed m));
        try exact CM; try apply Int.signed_range;
        try (change (-2147483648 <= 0 <= 2147483647); lia); try apply PTree.gss.
      rewrite PTree.gso by congruence; rewrite Int.repr_signed; exact M. }
    assert (FRAME : forall before mem tr exit mem', exec_stmt fe ge locals before mem body tr exit mem' Out_normal ->
      temp_agree [column;inner_bound] before exit).
    { intros; eapply structured_temp_frame;
        [exact (@runtime_body_writes d array row column stride body FLAT)|intros id _ BAD; exact BAD|eassumption]. }
    destruct (@frontend_iteration_decode fe ge locals _ memory column inner_bound body middle mem1 ACTIVE
      (@normal_statement_execution fe ge locals body (@runtime_body_normal d array row column stride body FLAT))
      FRAME INNER) as [first [first_mem [STORE REST]]].
    apply (flattened_singleton_execution FLAT) in STORE; inversion STORE; subst.
    match goal with LV : eval_lvalue _ _ _ _ (runtime_stride_lvalue _ _ _ _ _) _ _ _ |- _ =>
      destruct (runtime_stride_lvalue_domain LV) as [word LOOKUP]; exists word;
      cbn in LOOKUP |- *; rewrite PTree.gso in LOOKUP by congruence; exact LOOKUP end.
Qed.
Print Assumptions runtime_stride_domain_from_source.
