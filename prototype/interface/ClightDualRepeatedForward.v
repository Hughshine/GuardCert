From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightRedundantSet ClightNoWrap ClightPureExpr
  ClightCountedLoop ClightCountedProtocol ClightTempFrame ClightSameAddress ClightStraightLine.
From GuardInterface Require Import ClightReadonlyRewrite ClightReadonlyCellSwap ClightStableLoadBody
  ClightLoadedBoundSyntax ClightDualRepeatedSyntax ClightDualRepeatedGuard ClightDualRepeatedLoops ClightStoreIdempotence ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section REPEAT.
Variables row rows column columns out : ident.
Variables body outer : statement.
Hypothesis RC : row <> column.
Hypothesis RN : row <> rows.
Hypothesis RM : row <> columns.
Hypothesis RP : row <> out.
Hypothesis CN : column <> rows.
Hypothesis CM : column <> columns.
Hypothesis CP : column <> out.
Hypothesis BODY : flatten_region body = [dual_repeat_store out].
Hypothesis OUTER : flatten_region outer = [dual_repeat_reset column;loaded_bound_loop column columns body].

Theorem dual_repeat_known_execution fe ge locals le memory block ofs final :
  register_equals row Int.zero tt (Entry ge locals le memory) ->
  loaded_positive rows (Entry ge locals le memory) -> loaded_positive columns (Entry ge locals le memory) ->
  cell_pair_apart out rows (Entry ge locals le memory) -> cell_pair_apart out columns (Entry ge locals le memory) ->
  le ! out = Some (Vptr block ofs) -> Mem.storev Mint32 memory (Vptr block ofs) (Vint (Int.repr 0)) = Some final ->
  exists after,
    exec_stmt fe ge locals le memory (dual_repeat_source row rows outer) E0 after final Out_normal /\
    exec_stmt fe ge locals le memory (dual_repeat_candidate row rows column columns out) E0 after final Out_normal.
Proof.
  intros ZERO [upper [q [qo [Q [READ POS]]]]] [width [r [ro [R [READ2 POS2]]]]] APART APART2 P STORE.
  cbn [entry_temps entry_memory] in Q,READ,R,READ2.
  change (le ! row = Some (Vint Int.zero)) in ZERO.
  change (le ! out <> le ! rows) in APART; change (le ! out <> le ! columns) in APART2.
  assert (READ_FIXED : Mem.loadv Mint32 final (Vptr q qo) = Some (Vint upper)).
  { eapply mint32_load_survives_apart_store; [exact STORE|exact READ|congruence]. }
  assert (READ2_FIXED : Mem.loadv Mint32 final (Vptr r ro) = Some (Vint width)).
  { eapply mint32_load_survives_apart_store; [exact STORE|exact READ2|congruence]. }
  assert (FIXED : Mem.storev Mint32 final (Vptr block ofs) (Vint (Int.repr 0)) = Some final)
    by (eapply storev_result_fixed; exact STORE).
  assert (U : Int.signed upper <= Int.max_signed) by (pose proof (Int.signed_range upper); lia).
  assert (W : Int.signed width <= Int.max_signed) by (pose proof (Int.signed_range width); lia).
  assert (UZ : Z.of_nat (Z.to_nat (Int.signed upper)) = Int.signed upper) by (apply Z2Nat.id; lia).
  pose proof (@repeated_outer_encode fe ge locals row rows column columns out body outer block ofs q qo r ro
    (Int.signed upper) (Int.signed width) (Z.to_nat (Int.signed upper)) 0 le memory final
    RC RN RM RP CN CM CP BODY OUTER ltac:(lia) U ltac:(lia) ltac:(lia) ZERO Q R P
    ltac:(rewrite Int.repr_signed; exact READ) ltac:(rewrite Int.repr_signed; exact READ_FIXED)
    ltac:(rewrite Int.repr_signed; exact READ2) ltac:(rewrite Int.repr_signed; exact READ2_FIXED) STORE FIXED) as SOURCE.
  destruct (Z.to_nat (Int.signed upper)) eqn:COUNT; [cbn in UZ; lia|].
  change (exec_stmt fe ge locals le memory (dual_repeat_source row rows outer) E0
    (PTree.set row (Vint (Int.repr (Int.signed upper)))
      (PTree.set column (Vint (Int.repr (Int.signed width))) le)) final Out_normal) in SOURCE.
  rewrite !Int.repr_signed in SOURCE.
  exists (PTree.set row (Vint upper) (PTree.set column (Vint width) le)); split; [exact SOURCE|].
  unfold dual_repeat_candidate; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [eapply dual_repeat_store_encode; eassumption|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); apply exec_Sset;
    [apply eval_Elvalue with (loc := r) (ofs := ro) (bf := Full)|apply eval_Elvalue with (loc := q) (ofs := qo) (bf := Full)].
  - apply eval_Ederef,eval_Etempvar; exact R.
  - apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ2_FIXED].
  - apply eval_Ederef,eval_Etempvar; rewrite PTree.gso by congruence; exact Q.
  - apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ_FIXED].
Qed.
Theorem dual_repeat_forward fe entry observed : dual_repeat_domain row rows outer entry ->
  dual_repeat_premise row rows columns out entry ->
  clight_fragment_run fe (dual_repeat_source row rows outer) entry observed ->
  clight_fragment_run fe (dual_repeat_candidate row rows column columns out) entry observed.
Proof.
  destruct entry as [ge locals le memory], observed as [trace after final outcome].
  intros DOMAIN [ZERO [N [M [APART APART2]]]] SOURCE.
  destruct (@dual_repeat_first_store row rows column columns out body outer CM CP BODY OUTER fe ge locals le memory
    DOMAIN ZERO N M) as [block [ofs [fixed [P STORE]]]].
  destruct (@dual_repeat_known_execution fe ge locals le memory block ofs fixed ZERO N M APART APART2 P STORE)
    as [exit [KNOWN CANDIDATE]].
  destruct (@quiet_execution_determinate fe ge locals le memory (dual_repeat_source row rows outer)
    trace after final outcome SOURCE (@dual_repeat_source_quiet row rows out column columns body outer BODY OUTER)
    E0 exit fixed Out_normal KNOWN) as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst; exact CANDIDATE.
Qed.
End REPEAT.
Print Assumptions dual_repeat_known_execution.
Print Assumptions dual_repeat_forward.
