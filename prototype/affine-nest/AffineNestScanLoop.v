From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFramedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardAffineNest Require Import AffineNestScanModel.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The loop's upper bound can be below its initial value. Such a source child
    is empty and evaluates no leaf test, without normalizing its bound. *)
Theorem affine_boolean_scan_loop fe ge locals memory iterator bound flag body upper lower live base test :
  iterator<>bound -> iterator<>flag -> bound<>flag -> ~In iterator live ->
  signed_range upper -> signed_range lower ->
  (forall index temps accepted, signed_range index -> lower<=index<upper ->
    temps!iterator=Some(Vint(Int.repr index)) -> temps!bound=Some(Vint(Int.repr upper)) ->
    temps!flag=Some(memory_boolean_word accepted) -> temp_agree live base temps ->
    exists after, exec_stmt fe ge locals temps memory body E0 after memory Out_normal /\
      temp_agree(iterator::bound::live) temps after /\
      after!flag=Some(memory_boolean_word(accepted&&test index))) ->
  forall temps accepted,
    temps!iterator=Some(Vint(Int.repr lower)) -> temps!bound=Some(Vint(Int.repr upper)) ->
    temps!flag=Some(memory_boolean_word accepted) -> temp_agree live base temps ->
    exists after,
      exec_stmt fe ge locals temps memory(counted_loop iterator bound body) E0 after memory Out_normal /\
      temp_agree(bound::live) temps after /\
      after!flag=Some(memory_boolean_word(accepted&&memory_boolean_scan_result test lower(affine_scan_count lower upper))).
Proof.
  intros DISTINCT ITER_FLAG BOUND_FLAG FRESH UPPER LOWER BODY temps accepted ITER BOUND FLAG FRAME.
  destruct(Z_le_dec lower upper) as [ACTIVE|EMPTY].
  - destruct(@memory_boolean_scan_loop fe ge locals memory iterator bound flag body upper lower live base test
      DISTINCT ITER_FLAG BOUND_FLAG FRESH UPPER BODY(affine_scan_count lower upper) lower temps accepted)
      as [after [RUN [PUBLIC [EXIT GOOD]]]].
    + rewrite affine_scan_count_value; lia.
    + exact LOWER.
    + lia.
    + exact ITER.
    + exact BOUND.
    + exact FLAG.
    + exact FRAME.
    + exists after; auto.
  - exists temps; split.
    + unfold counted_loop; eapply exec_Sloop_stop1 with(out':=Out_break).
      * destruct(@counter_condition_at ge locals temps memory iterator bound lower upper DISTINCT ITER BOUND LOWER UPPER)
          as [value [EVAL BOOL]].
        assert(NO:(lower<?upper)=false) by(apply Z.ltb_ge; lia); rewrite NO in BOOL.
        eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
      * constructor.
    + split; [apply temp_agree_refl|].
      unfold affine_scan_count; rewrite Z.max_l by lia; cbn; rewrite andb_true_r; exact FLAG.
Qed.
Print Assumptions affine_boolean_scan_loop.
