From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

Lemma counter_temps_same iterator le x : le ! iterator = Some (Vint (Int.repr x)) ->
  counter_temps iterator le x = le.
Proof.
  intro LOOKUP; unfold counter_temps. apply PTree.extensionality; intro key.
  rewrite PTree.gsspec. destruct (peq key iterator); subst; congruence.
Qed.

Lemma counter_condition_at ge locals le m iterator bound x upper :
  iterator <> bound -> le ! iterator = Some (Vint (Int.repr x)) ->
  le ! bound = Some (Vint (Int.repr upper)) -> signed_range x -> signed_range upper ->
  expression_test (counter_condition iterator bound) (Entry ge locals le m) (x <? upper).
Proof.
  intros DISTINCT ITER BOUND RX RU.
  rewrite <- (@counter_temps_same iterator le x ITER).
  eapply counter_condition_run; eauto.
Qed.

Lemma counter_increment_at function_entry ge locals le m iterator x :
  le ! iterator = Some (Vint (Int.repr x)) -> signed_range x ->
  exec_stmt function_entry ge locals le m (counter_increment iterator) E0
    (counter_temps iterator le (x + 1)) m Out_normal.
Proof.
  intros ITER RX.
  pose proof (@counter_increment_run function_entry ge locals le m iterator x RX) as RUN.
  rewrite (@counter_temps_same iterator le x ITER) in RUN; exact RUN.
Qed.

(** A body can allocate and update its own scratch registers. It must preserve
    the outer counter, bound, and public frame at each iteration boundary. *)
Theorem framed_counted_loop_correct {S : Type} (body_sem : Z -> S -> S -> Prop)
  (view : S -> mem -> Prop) function_entry ge locals iterator bound body upper floor live base :
  iterator <> bound -> ~ In iterator live -> signed_range upper ->
  (forall x s0 s1 le m0, signed_range x -> floor <= x -> x < upper ->
    body_sem x s0 s1 -> view s0 m0 -> temp_agree live base le ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    exists le1 m1, view s1 m1 /\ temp_agree (iterator :: bound :: live) le le1 /\
      exec_stmt function_entry ge locals le m0 body E0 le1 m1 Out_normal) ->
  forall n x s0 s1 le m0, counted_iterations body_sem n x s0 s1 ->
    upper = x + Z.of_nat n -> signed_range x -> floor <= x -> view s0 m0 ->
    temp_agree live base le ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    exists le1 m1, view s1 m1 /\
      le1 ! iterator = Some (Vint (Int.repr upper)) /\
      le1 ! bound = Some (Vint (Int.repr upper)) /\ temp_agree live le le1 /\
      exec_stmt function_entry ge locals le m0 (counted_loop iterator bound body)
        E0 le1 m1 Out_normal.
Proof.
  intros DISTINCT FRESH RU BODY n x s0 s1 le m0 SOURCE.
  revert le m0; induction SOURCE; intros le m0 LENGTH RX FLOOR MEMORY FRAME0 ITER BOUND.
  - cbn in LENGTH. assert (EQ : upper = x) by lia; clear LENGTH; subst upper.
    exists le, m0; repeat split; auto using temp_agree_refl.
    unfold counted_loop. eapply exec_Sloop_stop1 with (out' := Out_break).
    + destruct (@counter_condition_at ge locals le m0 iterator bound x x
        DISTINCT ITER BOUND RX RU) as [v [EV BOOL]].
      rewrite Z.ltb_irrefl in BOOL; eapply exec_Sifthenelse; eauto; constructor.
    + constructor.
  - assert (LT : x < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    assert (RX' : signed_range (x + 1)) by (unfold signed_range in *; lia).
    destruct (BODY x s0 s1 le m0 RX FLOOR LT H MEMORY FRAME0 ITER BOUND)
      as [middle [m1 [MEMORY1 [FRAME EXEC1]]]].
    assert (ITER1 : middle ! iterator = Some (Vint (Int.repr x))).
    { rewrite FRAME by (cbn; auto); exact ITER. }
    assert (BOUND1 : middle ! bound = Some (Vint (Int.repr upper))).
    { rewrite FRAME by (cbn; auto); exact BOUND. }
    assert (BOUND2 : (counter_temps iterator middle (x + 1)) ! bound =
      Some (Vint (Int.repr upper))).
    { unfold counter_temps; rewrite PTree.gso by congruence; exact BOUND1. }
    assert (FRAME1 : temp_agree live base (counter_temps iterator middle (x + 1))).
    { eapply temp_agree_trans; [exact FRAME0 |].
      eapply temp_agree_trans; [|apply temp_agree_set; exact FRESH].
      eapply temp_agree_weaken; [|exact FRAME]; cbn; auto. }
    destruct (IHSOURCE (counter_temps iterator middle (x + 1)) m1)
      as [final [m2 [MEMORY2 [ITER2 [BOUND3 [FRAME2 EXEC2]]]]]];
      auto; [rewrite Nat2Z.inj_succ in LENGTH; lia | lia | apply PTree.gss |].
    exists final, m2; repeat split; auto.
    + eapply temp_agree_trans; [|exact FRAME2].
      eapply temp_agree_trans; [|apply temp_agree_set; exact FRESH].
      eapply temp_agree_weaken; [|exact FRAME]; cbn; auto.
    + unfold counted_loop. eapply exec_Sloop_loop with (out1 := Out_normal)
        (t1 := E0) (t2 := E0) (t3 := E0).
      * destruct (@counter_condition_at ge locals le m0 iterator bound x upper
          DISTINCT ITER BOUND RX RU) as [v [EV BOOL]].
        assert (CHECK : (x <? upper) = true) by (apply Z.ltb_lt; exact LT).
        rewrite CHECK in BOOL. eapply exec_Sifthenelse with (b := true);
          [exact EV | exact BOOL | exact EXEC1].
      * constructor.
      * apply counter_increment_at with (x := x); auto.
      * exact EXEC2.
Qed.

Print Assumptions framed_counted_loop_correct.
