From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightRedundantSet
  ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol ClightFramedLoop ClightLoopExecution ClightTempFrame ClightStraightLine.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedBoundGuard ClightDualLoadedUnitSyntax
  ClightStrictLoopProgress ClightDualRepeatedSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition repeated_memory count (before fixed : mem) := match count with O => before | S _ => fixed end.
Lemma repeat_range upper x : 0 <= x <= upper -> upper <= Int.max_signed -> signed_range x.
Proof. unfold signed_range; change Int.min_signed with (-2147483648); lia. Qed.
Lemma repeat_less upper x : signed_range upper -> signed_range x -> x < upper -> Int.lt (Int.repr x) (Int.repr upper) = true.
Proof.
  intros U X LT; unfold Int.lt; rewrite !Int.signed_repr by assumption; destruct (zlt x upper); [reflexivity|lia].
Qed.
Theorem repeated_inner_encode fe ge locals iterator parameter out body block ofs q qo upper count x le before fixed :
  iterator <> parameter -> iterator <> out -> flatten_region body = [dual_repeat_store out] ->
  0 <= x -> upper <= Int.max_signed -> upper = x + Z.of_nat count ->
  le ! iterator = Some (Vint (Int.repr x)) -> le ! parameter = Some (Vptr q qo) -> le ! out = Some (Vptr block ofs) ->
  Mem.loadv Mint32 before (Vptr q qo) = Some (Vint (Int.repr upper)) ->
  Mem.loadv Mint32 fixed (Vptr q qo) = Some (Vint (Int.repr upper)) ->
  Mem.storev Mint32 before (Vptr block ofs) (Vint (Int.repr 0)) = Some fixed ->
  Mem.storev Mint32 fixed (Vptr block ofs) (Vint (Int.repr 0)) = Some fixed ->
  exec_stmt fe ge locals le before (loaded_bound_loop iterator parameter body) E0
    (PTree.set iterator (Vint (Int.repr upper)) le) (repeated_memory count before fixed) Out_normal.
Proof.
  intros IP IO BODY; revert x le before.
  induction count as [|count IH]; intros x le before LOW MAX LENGTH I Q P READ READ_FIXED STORE FIXED.
  - assert (U_EQ : upper=x) by (cbn in LENGTH; lia); clear LENGTH; subst upper; unfold repeated_memory.
    assert (SAME : PTree.set iterator (Vint (Int.repr x)) le = le) by (apply counter_temps_same; exact I).
    rewrite SAME; apply strict_zero_trip_encode.
    assert (TEST : Int.lt (Int.repr x) (Int.repr x) = false) by
      (unfold Int.lt; destruct (zlt _ _); [lia|reflexivity]).
    rewrite <- TEST; eapply loaded_bound_test_eval; eassumption.
  - assert (X : signed_range x) by (apply repeat_range with (upper := upper); lia).
    assert (U : signed_range upper) by (apply repeat_range with (upper := upper); lia).
    assert (LT : x < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    assert (NEXT : increment_temps iterator le = PTree.set iterator (Vint (Int.repr (x+1))) le)
      by (apply counter_increment_small; exact I).
    assert (TAIL : exec_stmt fe ge locals (increment_temps iterator le) fixed
      (loaded_bound_loop iterator parameter body) E0
      (PTree.set iterator (Vint (Int.repr upper)) le) fixed Out_normal).
    { rewrite NEXT.
      pose proof (IH (x+1) (PTree.set iterator (Vint (Int.repr (x+1))) le) fixed
        ltac:(lia) MAX ltac:(rewrite Nat2Z.inj_succ in LENGTH; lia)
        (PTree.gss _ _ _) ltac:(rewrite PTree.gso by congruence; exact Q)
        ltac:(rewrite PTree.gso by congruence; exact P) READ_FIXED READ_FIXED FIXED FIXED) as RUN.
      rewrite PTree.set2 in RUN; destruct count; exact RUN. }
    unfold loaded_bound_loop; eapply strict_iteration_encode with (body_temps := le) (body_memory := fixed).
    + rewrite <- (repeat_less U X LT); eapply loaded_bound_test_eval; eassumption.
    + exists (Int.repr x); split; [exact I|rewrite Int.signed_repr by exact X; lia].
    + eapply flattened_singleton_encode; [exact BODY|eapply dual_repeat_store_encode; eassumption].
    + exact TAIL.
Qed.

Definition repeated_outer_exit row column upper width count le :=
  PTree.set row (Vint (Int.repr upper))
    (match count with O => le | S _ => PTree.set column (Vint (Int.repr width)) le end).
Theorem repeated_outer_encode fe ge locals row rows column columns out body outer block ofs q qo r ro
  upper width count x le before fixed :
  row <> column -> row <> rows -> row <> columns -> row <> out ->
  column <> rows -> column <> columns -> column <> out ->
  flatten_region body = [dual_repeat_store out] ->
  flatten_region outer = [dual_repeat_reset column;loaded_bound_loop column columns body] ->
  0 <= x -> upper <= Int.max_signed -> 0 < width <= Int.max_signed -> upper = x + Z.of_nat count ->
  le ! row = Some (Vint (Int.repr x)) -> le ! rows = Some (Vptr q qo) ->
  le ! columns = Some (Vptr r ro) -> le ! out = Some (Vptr block ofs) ->
  Mem.loadv Mint32 before (Vptr q qo) = Some (Vint (Int.repr upper)) ->
  Mem.loadv Mint32 fixed (Vptr q qo) = Some (Vint (Int.repr upper)) ->
  Mem.loadv Mint32 before (Vptr r ro) = Some (Vint (Int.repr width)) ->
  Mem.loadv Mint32 fixed (Vptr r ro) = Some (Vint (Int.repr width)) ->
  Mem.storev Mint32 before (Vptr block ofs) (Vint (Int.repr 0)) = Some fixed ->
  Mem.storev Mint32 fixed (Vptr block ofs) (Vint (Int.repr 0)) = Some fixed ->
  exec_stmt fe ge locals le before (dual_repeat_source row rows outer) E0
    (repeated_outer_exit row column upper width count le) (repeated_memory count before fixed) Out_normal.
Proof.
  intros RC RN RM RP CN CM CP BODY OUTER; revert x le before.
  induction count as [|count IH]; intros x le before LOW MAX WIDTH LENGTH I Q R P READ READ_FIXED READ2 READ2_FIXED STORE FIXED.
  - assert (U_EQ : upper=x) by (cbn in LENGTH; lia); clear LENGTH; subst upper; unfold repeated_outer_exit,repeated_memory.
    assert (SAME : PTree.set row (Vint (Int.repr x)) le = le) by (apply counter_temps_same; exact I).
    rewrite SAME; apply strict_zero_trip_encode.
    assert (TEST : Int.lt (Int.repr x) (Int.repr x) = false) by
      (unfold Int.lt; destruct (zlt _ _); [lia|reflexivity]).
    rewrite <- TEST; eapply loaded_bound_test_eval; eassumption.
  - assert (X : signed_range x) by (apply repeat_range with (upper := upper); lia).
    assert (U : signed_range upper) by (apply repeat_range with (upper := upper); lia).
    assert (LT : x < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    set (middle := PTree.set column (Vint (Int.repr width)) le).
    assert (INNER : exec_stmt fe ge locals (PTree.set column (Vint Int.zero) le) before
      (loaded_bound_loop column columns body) E0 middle fixed Out_normal).
    { pose proof (@repeated_inner_encode fe ge locals column columns out body block ofs r ro width (Z.to_nat width) 0
        (PTree.set column (Vint Int.zero) le) before fixed CM CP BODY ltac:(lia) ltac:(lia)
        ltac:(rewrite Z2Nat.id by lia; lia) (PTree.gss _ _ _)
        ltac:(rewrite PTree.gso by congruence; exact R) ltac:(rewrite PTree.gso by congruence; exact P)
        READ2 READ2_FIXED STORE FIXED) as RUN.
      rewrite PTree.set2 in RUN; unfold middle.
      assert (WZ : Z.of_nat (Z.to_nat width) = width) by (apply Z2Nat.id; lia).
      destruct (Z.to_nat width) eqn:COUNT; [cbn in WZ; lia|exact RUN]. }
    assert (BODY_RUN : exec_stmt fe ge locals le before outer E0 middle fixed Out_normal).
    { eapply flattened_pair_encode; [exact OUTER| |exact INNER]. apply exec_Sset; constructor. }
    assert (ROW : middle ! row = Some (Vint (Int.repr x)))
      by (unfold middle; rewrite PTree.gso by congruence; exact I).
    assert (NEXT : increment_temps row middle = PTree.set row (Vint (Int.repr (x+1))) middle)
      by (apply counter_increment_small; exact ROW).
    assert (TAIL : exec_stmt fe ge locals (increment_temps row middle) fixed
      (dual_repeat_source row rows outer) E0 (repeated_outer_exit row column upper width (S count) le) fixed Out_normal).
    { rewrite NEXT.
      pose proof (IH (x+1) (PTree.set row (Vint (Int.repr (x+1))) middle) fixed
        ltac:(lia) MAX WIDTH ltac:(rewrite Nat2Z.inj_succ in LENGTH; lia)
        (PTree.gss _ _ _) ltac:(unfold middle; repeat rewrite PTree.gso by congruence; exact Q)
        ltac:(unfold middle; repeat rewrite PTree.gso by congruence; exact R)
        ltac:(unfold middle; repeat rewrite PTree.gso by congruence; exact P)
        READ_FIXED READ_FIXED READ2_FIXED READ2_FIXED FIXED FIXED) as RUN.
      assert (EXIT : repeated_outer_exit row column upper width count
          (PTree.set row (Vint (Int.repr (x+1))) middle) = repeated_outer_exit row column upper width (S count) le).
      { destruct count; unfold repeated_outer_exit,middle; apply PTree.extensionality; intro key; rewrite !PTree.gsspec;
          destruct (peq key row), (peq key column); subst; intuition congruence. }
      rewrite EXIT in RUN; destruct count; exact RUN. }
    unfold dual_repeat_source,loaded_bound_loop; eapply strict_iteration_encode with
      (body_temps := middle) (body_memory := fixed).
    + rewrite <- (repeat_less U X LT); eapply loaded_bound_test_eval; eassumption.
    + exists (Int.repr x); split; [exact ROW|rewrite Int.signed_repr by exact X; lia].
    + exact BODY_RUN.
    + exact TAIL.
Qed.
Print Assumptions repeated_inner_encode.
Print Assumptions repeated_outer_encode.
