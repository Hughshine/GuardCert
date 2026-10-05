From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightRedundantSet ClightCountedLoop
  ClightCountedProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax ClightRegionProgress
  ClightTempFrame ClightStraightLine.
From GuardInterface Require Import ClightReadonlyRewrite ClightStrictLoopProgress ClightLoadedBoundSyntax
  ClightReadonlyCellSwap ClightStableLoadBody ClightDualLoadedUnitSyntax ClightDualLoadedUnitGuard ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.

Section UNIT.
Variables row rows column columns out : ident.
Variables body outer : statement.
Hypothesis RC : row <> column.
Hypothesis RN : row <> rows.
Hypothesis RM : row <> columns.
Hypothesis RP : row <> out.
Hypothesis CN : column <> rows.
Hypothesis CM : column <> columns.
Hypothesis CP : column <> out.
Hypothesis BODY : flatten_region body = [dual_unit_store out].
Hypothesis OUTER : flatten_region outer = [dual_unit_reset column; loaded_bound_loop column columns body].

Theorem dual_unit_known_execution fe ge locals le memory b ofs final :
  register_equals row Int.zero tt (Entry ge locals le memory) ->
  loaded_one rows (Entry ge locals le memory) -> loaded_one columns (Entry ge locals le memory) ->
  cell_pair_apart out rows (Entry ge locals le memory) -> cell_pair_apart out columns (Entry ge locals le memory) ->
  le ! out = Some (Vptr b ofs) -> Mem.storev Mint32 memory (Vptr b ofs) (Vint (Int.repr 2)) = Some final ->
  exec_stmt fe ge locals le memory (dual_unit_source row rows outer) E0
    (PTree.set row (Vint Int.one) (PTree.set column (Vint Int.one) le)) final Out_normal /\
  exec_stmt fe ge locals le memory (dual_unit_candidate row column out) E0
    (PTree.set row (Vint Int.one) (PTree.set column (Vint Int.one) le)) final Out_normal.
Proof.
  intros ZERO [q [qo [Q READ]]] [r [ro [R READ2]]] APART APART2 P STORE.
  cbn [entry_temps entry_memory] in Q, READ, R, READ2.
  change (le ! row = Some (Vint Int.zero)) in ZERO.
  change (le ! out <> le ! rows) in APART.
  change (le ! out <> le ! columns) in APART2.
  assert (READ_FINAL : Mem.loadv Mint32 final (Vptr q qo) = Some (Vint Int.one)).
  { eapply mint32_load_survives_apart_store; [exact STORE|exact READ|congruence]. }
  assert (READ_FINAL2 : Mem.loadv Mint32 final (Vptr r ro) = Some (Vint Int.one)).
  { eapply mint32_load_survives_apart_store; [exact STORE|exact READ2|congruence]. }
  assert (INC_COL : increment_temps column (PTree.set column (Vint Int.zero) le) = PTree.set column (Vint Int.one) le).
  { unfold increment_temps; rewrite PTree.gss; change (Int.add Int.zero Int.one) with Int.one; apply PTree.set2. }
  assert (INC_ROW : increment_temps row (PTree.set column (Vint Int.one) le) =
    PTree.set row (Vint Int.one) (PTree.set column (Vint Int.one) le)).
  { unfold increment_temps; rewrite PTree.gso by congruence; rewrite ZERO;
      change (Int.add Int.zero Int.one) with Int.one; reflexivity. }
  assert (INNER : exec_stmt fe ge locals (PTree.set column (Vint Int.zero) le) memory
    (loaded_bound_loop column columns body) E0 (PTree.set column (Vint Int.one) le) final Out_normal).
  { unfold loaded_bound_loop; eapply strict_iteration_encode with
      (body_temps := PTree.set column (Vint Int.zero) le) (body_memory := final).
    - change true with (Int.lt Int.zero Int.one); eapply loaded_bound_test_eval;
        [apply PTree.gss|rewrite PTree.gso by congruence; exact R|exact READ2].
    - exists Int.zero; split; [apply PTree.gss|change (0 < 2147483647)%Z; lia].
    - eapply flattened_singleton_encode; [exact BODY|].
      eapply dual_unit_store_encode; [rewrite PTree.gso by congruence; exact P|exact STORE].
    - rewrite INC_COL; apply strict_zero_trip_encode.
      change false with (Int.lt Int.one Int.one); eapply loaded_bound_test_eval;
        [apply PTree.gss|rewrite PTree.gso by congruence; exact R|exact READ_FINAL2]. }
  assert (OUTER_RUN : exec_stmt fe ge locals le memory outer E0
    (PTree.set column (Vint Int.one) le) final Out_normal).
  { eapply flattened_pair_encode; [exact OUTER| |exact INNER].
    apply exec_Sset; constructor. }
  split.
  - unfold dual_unit_source, loaded_bound_loop; eapply strict_iteration_encode with
      (body_temps := PTree.set column (Vint Int.one) le) (body_memory := final).
    + change true with (Int.lt Int.zero Int.one); eapply loaded_bound_test_eval; eassumption.
    + exists Int.zero; split; [rewrite PTree.gso by congruence; exact ZERO|change (0 < 2147483647)%Z; lia].
    + exact OUTER_RUN.
    + rewrite INC_ROW; apply strict_zero_trip_encode.
      change false with (Int.lt Int.one Int.one); eapply loaded_bound_test_eval;
        [apply PTree.gss|repeat rewrite PTree.gso by congruence; exact Q|exact READ_FINAL].
  - unfold dual_unit_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply dual_unit_store_encode; eassumption.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); apply exec_Sset; constructor.
Qed.

Theorem dual_unit_forward fe entry observed : dual_unit_domain row rows outer entry ->
  dual_unit_premise row rows columns out entry ->
  clight_fragment_run fe (dual_unit_source row rows outer) entry observed ->
  clight_fragment_run fe (dual_unit_candidate row column out) entry observed.
Proof.
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  intros DOMAIN [ZERO [ONE [TWO [APART APART2]]]] SOURCE.
  destruct (@dual_unit_first_store row rows column columns out body outer CM CP BODY OUTER fe ge locals le memory
    DOMAIN ZERO ONE TWO) as [b [ofs [mem [P STORE]]]].
  destruct (@dual_unit_known_execution fe ge locals le memory b ofs mem ZERO ONE TWO APART APART2 P STORE)
    as [KNOWN CANDIDATE].
  destruct (@quiet_execution_determinate fe ge locals le memory (dual_unit_source row rows outer)
    trace after final outcome SOURCE (@dual_unit_source_quiet row rows out column columns body outer BODY OUTER)
    E0 (PTree.set row (Vint Int.one) (PTree.set column (Vint Int.one) le)) mem Out_normal KNOWN)
    as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst; exact CANDIDATE.
Qed.
End UNIT.

Print Assumptions dual_unit_known_execution.
Print Assumptions dual_unit_forward.
