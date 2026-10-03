From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFramedLoop ClightTempFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A bounded loop accumulates a Boolean result in a private temporary.
    Its body can use other private state, but preserves the iteration boundary,
    loop bound, public temporaries, and memory. No source data is read here. *)
Definition memory_boolean_word (accepted : bool) := Vint (if accepted then Int.one else Int.zero).

Fixpoint memory_boolean_scan_result (test : Z -> bool) (start : Z) (count : nat) := match count with
  | O => true
  | S rest => test start && memory_boolean_scan_result test (start+1) rest
  end.

Lemma memory_boolean_scan_ext first second :
  (forall index, first index = second index) -> forall count start,
    memory_boolean_scan_result first start count = memory_boolean_scan_result second start count.
Proof. intros SAME count; induction count; intro start; cbn; [reflexivity|rewrite SAME,IHcount; reflexivity]. Qed.

Lemma memory_boolean_scan_member test start count :
  memory_boolean_scan_result test start count = true <->
  forall index, start <= index < start + Z.of_nat count -> test index = true.
Proof.
  revert start; induction count; intro start; cbn [memory_boolean_scan_result].
  - split; [intros _ index RANGE; lia|reflexivity].
  - rewrite andb_true_iff,IHcount,Nat2Z.inj_succ; split.
    + intros [FIRST REST] index RANGE; destruct (Z.eq_dec index start); subst; [exact FIRST|apply REST; lia].
    + intro ALL; split; [apply ALL; lia|intros index RANGE; apply ALL; lia].
Qed.

Theorem memory_boolean_scan_loop fe ge locals memory iterator bound flag body upper floor live base test :
  iterator <> bound -> iterator <> flag -> bound <> flag -> ~ In iterator live ->
  signed_range upper ->
  (forall index temps accepted, signed_range index -> floor <= index < upper ->
    temps ! iterator = Some (Vint (Int.repr index)) ->
    temps ! bound = Some (Vint (Int.repr upper)) ->
    temps ! flag = Some (memory_boolean_word accepted) -> temp_agree live base temps ->
    exists after,
      exec_stmt fe ge locals temps memory body E0 after memory Out_normal /\
      temp_agree (iterator::bound::live) temps after /\
      after ! flag = Some (memory_boolean_word (accepted && test index))) ->
  forall count start temps accepted,
    upper = start + Z.of_nat count -> signed_range start -> floor <= start ->
    temps ! iterator = Some (Vint (Int.repr start)) ->
    temps ! bound = Some (Vint (Int.repr upper)) ->
    temps ! flag = Some (memory_boolean_word accepted) -> temp_agree live base temps ->
    exists after,
      exec_stmt fe ge locals temps memory (counted_loop iterator bound body) E0 after memory Out_normal /\
      temp_agree (bound::live) temps after /\
      after ! iterator = Some (Vint (Int.repr upper)) /\
      after ! flag = Some (memory_boolean_word (accepted && memory_boolean_scan_result test start count)).
Proof.
  intros DISTINCT FLAG_BOUND FLAG_COUNTER FRESH UPPER BODY count.
  induction count as [|count IH]; intros start temps accepted LENGTH START FLOOR ITER BOUND FLAG INPUT_FRAME.
  - cbn in LENGTH; assert (SAME : upper = start) by lia; clear LENGTH; subst upper.
    exists temps; repeat split; auto using temp_agree_refl.
    + unfold counted_loop; eapply exec_Sloop_stop1 with (out' := Out_break).
      * destruct (@counter_condition_at ge locals temps memory iterator bound start start
          DISTINCT ITER BOUND START UPPER) as [value [EVAL BOOL]].
        rewrite Z.ltb_irrefl in BOOL; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
      * constructor.
    + cbn [memory_boolean_scan_result]; rewrite andb_true_r; exact FLAG.
  - assert (RANGE : floor <= start < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    destruct (BODY start temps accepted START RANGE ITER BOUND FLAG INPUT_FRAME)
      as [middle [RUN [FRAME NEXT_FLAG]]].
    assert (MID_ITER : middle ! iterator = Some (Vint (Int.repr start))) by
      (rewrite FRAME by (cbn; auto); exact ITER).
    assert (MID_BOUND : middle ! bound = Some (Vint (Int.repr upper))) by
      (rewrite FRAME by (cbn; auto); exact BOUND).
    assert (NEXT_START : signed_range (start+1)) by (unfold signed_range in *; lia).
    destruct (IH (start+1) (counter_temps iterator middle (start+1)) (accepted && test start))
      as [after [REST [REST_FRAME [EXIT EXIT_FLAG]]]].
    + rewrite Nat2Z.inj_succ in LENGTH; lia.
    + exact NEXT_START.
    + lia.
    + unfold counter_temps; apply PTree.gss.
    + unfold counter_temps; rewrite PTree.gso by congruence; exact MID_BOUND.
    + unfold counter_temps; rewrite PTree.gso by congruence; exact NEXT_FLAG.
    + eapply temp_agree_trans; [exact INPUT_FRAME|].
      eapply temp_agree_trans; [|apply temp_agree_set; exact FRESH].
      eapply temp_agree_weaken; [|exact FRAME]; cbn; auto.
    + exists after; split.
      * unfold counted_loop; eapply exec_Sloop_loop with (out1 := Out_normal) (t1 := E0) (t2 := E0) (t3 := E0).
        -- destruct (@counter_condition_at ge locals temps memory iterator bound start upper
            DISTINCT ITER BOUND START UPPER) as [value [EVAL BOOL]].
           assert (LT : (start <? upper) = true) by (apply Z.ltb_lt; lia).
           rewrite LT in BOOL; eapply exec_Sifthenelse; [exact EVAL|exact BOOL|exact RUN].
        -- constructor.
        -- exact (@counter_increment_at fe ge locals middle memory iterator start MID_ITER START).
        -- exact REST.
      * split.
        -- eapply temp_agree_trans; [|exact REST_FRAME].
           eapply temp_agree_trans.
           ++ eapply temp_agree_weaken; [|exact FRAME]; cbn; auto.
           ++ apply temp_agree_set; cbn; intros [BAD|BAD]; [congruence|apply FRESH; exact BAD].
        -- split; [exact EXIT|cbn [memory_boolean_scan_result]; rewrite andb_assoc; exact EXIT_FLAG].
Qed.

Definition memory_boolean_test_body flag expression :=
  Sifthenelse expression Sskip (Sset flag (Econst_int Int.zero type_int32s)).

Lemma memory_boolean_test_body_execution fe ge locals temps memory flag expression accepted result live :
  ~ In flag live -> temps ! flag = Some (memory_boolean_word accepted) ->
  expression_test expression (Entry ge locals temps memory) result ->
  exists after,
    exec_stmt fe ge locals temps memory (memory_boolean_test_body flag expression) E0 after memory Out_normal /\
    temp_agree live temps after /\
    after ! flag = Some (memory_boolean_word (accepted && result)).
Proof.
  intros FRESH FLAG [value [EVAL BOOL]]; unfold memory_boolean_test_body.
  destruct result.
  - exists temps; split; [eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor]|].
    split; [apply temp_agree_refl|rewrite andb_true_r; exact FLAG].
  - exists (PTree.set flag (Vint Int.zero) temps); split.
    + eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor; constructor].
    + split; [apply temp_agree_set; exact FRESH|rewrite andb_false_r; apply PTree.gss].
Qed.

Print Assumptions memory_boolean_scan_loop.
Print Assumptions memory_boolean_test_body_execution.
