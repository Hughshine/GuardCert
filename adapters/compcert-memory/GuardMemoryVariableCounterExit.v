From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightFramedLoop
  ClightFrontendLoopProtocol ClightFrontendRegion ClightCountedProtocol
  ClightLoopSyntax ClightZeroTrip ClightLoopExecution ClightParametricLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_counter_exit iterator (settle : Z -> temp_env -> temp_env) count x temps :=
  match count with
  | O => temps
  | S rest => memory_counter_exit iterator settle rest (x+1)
      (PTree.set iterator (Vint (Int.repr (x+1))) (settle x temps)) end.

Section DECODE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable iterator bound : ident.
Variable body : statement.
Variable settle : Z -> temp_env -> temp_env.
Variable body_sem : Z -> mem -> mem -> Prop.
Variable floor upper : Z.
Variable stable : list ident.
Variable base : temp_env.
Hypothesis DISTINCT : iterator <> bound.
Hypothesis NORMAL : normal_statement body = true.
Hypothesis HEADERS : forall before memory trace after final,
  exec_stmt fe ge locals before memory body trace after final Out_normal ->
  temp_agree [iterator;bound] before after.
Hypothesis SETTLE_BOUND : forall x temps, (settle x temps) ! bound = temps ! bound.
Hypothesis SETTLE_STABLE : forall x temps, temp_agree stable temps (settle x temps).
Hypothesis ITER_STABLE : ~ In iterator stable.
Hypothesis UPPER : signed_range upper.

Theorem frontend_variable_settle_decode
  (DECODE : forall x temps memory after final, floor <= x < upper ->
    temps ! iterator = Some (Vint (Int.repr x)) -> temps ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base temps ->
    exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
    body_sem x memory final /\ after = settle x temps) :
  forall count x temps memory after final, upper = x+Z.of_nat count -> signed_range x -> floor <= x ->
    temps ! iterator = Some (Vint (Int.repr x)) -> temps ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base temps ->
    exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
    counted_iterations body_sem count x memory final /\ after = memory_counter_exit iterator settle count x temps.
Proof.
  induction count as [|count IH]; intros x temps memory after final LENGTH RANGE FLOOR ITER BOUND FRAME RUN.
  - cbn in LENGTH; assert (SAME : upper = x) by lia; clear LENGTH; subst upper.
    pose proof (@counter_condition_at ge locals temps memory iterator bound x x
      DISTINCT ITER BOUND RANGE UPPER) as TEST; rewrite Z.ltb_irrefl in TEST.
    destruct (frontend_zero_trip_result RUN TEST) as [TEMPS MEMORY]; subst.
    split; [constructor|reflexivity].
  - assert (LT : x < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    pose proof (@counter_condition_at ge locals temps memory iterator bound x upper
      DISTINCT ITER BOUND RANGE UPPER) as TEST.
    assert (TRUE : (x <? upper) = true) by (apply Z.ltb_lt; exact LT); rewrite TRUE in TEST.
    destruct (frontend_iteration_decode TEST (@normal_statement_execution fe ge locals body NORMAL) HEADERS RUN)
      as [middle [m1 [BODY REST]]].
    assert (ITER_BODY : middle ! iterator = Some (Vint (Int.repr x))).
    { rewrite (@HEADERS temps memory E0 middle m1 BODY iterator ltac:(cbn; auto)); exact ITER. }
    destruct (DECODE x temps memory middle m1 ltac:(lia) ITER BOUND FRAME BODY) as [STEP SETTLED].
    subst middle.
    rewrite (@counter_increment_small iterator (settle x temps) x ITER_BODY) in REST.
    assert (N1 : (PTree.set iterator (Vint (Int.repr (x+1))) (settle x temps)) ! bound =
      Some (Vint (Int.repr upper))).
    { rewrite PTree.gso by congruence; rewrite SETTLE_BOUND; exact BOUND. }
    assert (FRAME1 : temp_agree stable base
      (PTree.set iterator (Vint (Int.repr (x+1))) (settle x temps))).
    { eapply temp_agree_trans; [exact FRAME|].
      eapply temp_agree_trans; [apply SETTLE_STABLE|apply temp_agree_set; exact ITER_STABLE]. }
    destruct (IH (x+1) (PTree.set iterator (Vint (Int.repr (x+1))) (settle x temps))
      m1 after final ltac:(rewrite Nat2Z.inj_succ in LENGTH; lia)
      ltac:(unfold signed_range in *; lia) ltac:(lia) (PTree.gss _ _ _) N1 FRAME1 REST) as [TAIL EXIT].
    split; [econstructor; eauto|exact EXIT].
Qed.
End DECODE.
Print Assumptions frontend_variable_settle_decode.
