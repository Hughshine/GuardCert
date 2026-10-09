From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryDoubleLocations GuardMemoryObservationDeterminism.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_long_increment iterator :=
  Sset iterator (memory_long_plus_int (Etempvar iterator memory_long_type) 1).
Definition memory_long_frontend_loop iterator condition body :=
  Sloop (Ssequence (Sifthenelse condition Sskip Sbreak) body) (memory_long_increment iterator).
Definition memory_long_initialized_loop iterator condition body :=
  Ssequence (Sset iterator memory_long_zero) (memory_long_frontend_loop iterator condition body).

Lemma memory_expression_test_unique condition ge locals temps memory first second :
  expression_test condition (Entry ge locals temps memory) first ->
  expression_test condition (Entry ge locals temps memory) second -> first=second.
Proof.
  intros [a [A BOOLA]] [b [B BOOLB]].
  pose proof (memory_expression_unique A B) as SAME; subst b; congruence.
Qed.

Lemma memory_long_increment_exact fe ge locals temps memory iterator value trace final_temps final outcome :
  temps ! iterator = Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory (memory_long_increment iterator) trace final_temps final outcome ->
  trace=E0 /\ final_temps=PTree.set iterator (Vlong (Int64.repr (value+1))) temps /\
  final=memory /\ outcome=Out_normal.
Proof.
  intros TEMP RUN.
  assert (INPUT : eval_expr ge locals temps memory (Etempvar iterator memory_long_type) (Vlong (Int64.repr value)))
    by (constructor; exact TEMP).
  pose proof (@memory_long_plus_int_execution ge locals temps memory
    (Etempvar iterator memory_long_type) value 1 eq_refl
    ltac:(change (-2147483648 <= 1 <= 2147483647); lia) INPUT) as EXPECTED.
  unfold memory_long_increment in RUN; inversion RUN; subst.
  pose proof (memory_expression_unique H8 EXPECTED) as SAME; subst v.
  repeat split; reflexivity.
Qed.

Lemma memory_long_header_decode fe ge locals temps memory condition body trace final_temps final outcome :
  exec_stmt fe ge locals temps memory (Ssequence (Sifthenelse condition Sskip Sbreak) body)
    trace final_temps final outcome ->
  exists flag, expression_test condition (Entry ge locals temps memory) flag /\
    if flag then exec_stmt fe ge locals temps memory body trace final_temps final outcome
    else trace=E0 /\ final_temps=temps /\ final=memory /\ outcome=Out_break.
Proof.
  intro RUN; inversion RUN; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
    inversion HEADER; subst;
    match goal with BRANCH : exec_stmt _ _ _ _ _ (if ?flag then Sskip else Sbreak) _ _ _ _ |- _ =>
      assert (TEST : expression_test condition (Entry ge locals temps memory) flag)
        by (eexists; split; eassumption);
      destruct flag; inversion BRANCH; subst
    end
  end.
  - exists true; cbn in *; auto.
  - contradiction.
  - exists false; split; [exact TEST|repeat split; reflexivity].
Qed.

Lemma memory_long_header_true fe ge locals temps memory condition body trace final_temps final outcome :
  expression_test condition (Entry ge locals temps memory) true ->
  exec_stmt fe ge locals temps memory (Ssequence (Sifthenelse condition Sskip Sbreak) body)
    trace final_temps final outcome ->
  exec_stmt fe ge locals temps memory body trace final_temps final outcome.
Proof.
  intros TEST RUN; destruct (memory_long_header_decode RUN) as [flag [CHECK REST]].
  pose proof (memory_expression_test_unique CHECK TEST) as FLAG; subst flag; exact REST.
Qed.
Lemma memory_long_header_false fe ge locals temps memory condition body trace final_temps final outcome :
  expression_test condition (Entry ge locals temps memory) false ->
  exec_stmt fe ge locals temps memory (Ssequence (Sifthenelse condition Sskip Sbreak) body)
    trace final_temps final outcome ->
  trace=E0 /\ final_temps=temps /\ final=memory /\ outcome=Out_break.
Proof.
  intros TEST RUN; destruct (memory_long_header_decode RUN) as [flag [CHECK REST]].
  pose proof (memory_expression_test_unique CHECK TEST) as FLAG; subst flag; exact REST.
Qed.

Lemma memory_long_loop_stop_execution fe ge locals temps memory iterator condition body :
  expression_test condition (Entry ge locals temps memory) false ->
  exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body)
    E0 temps memory Out_normal.
Proof.
  intros [value [EVAL BOOL]]; unfold memory_long_frontend_loop.
  eapply exec_Sloop_stop1 with (out':=Out_break); [|constructor].
  eapply exec_Sseq_2; [eapply exec_Sifthenelse with (b:=false); [exact EVAL|exact BOOL|constructor]|discriminate].
Qed.
Lemma memory_long_loop_stop_decode fe ge locals temps memory iterator condition body trace final_temps final outcome :
  expression_test condition (Entry ge locals temps memory) false ->
  exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body)
    trace final_temps final outcome ->
  trace=E0 /\ final_temps=temps /\ final=memory /\ outcome=Out_normal.
Proof.
  intros TEST RUN; inversion RUN; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Ssequence (Sifthenelse _ _ _) _) _ _ _ _ |- _ =>
    pose proof (memory_long_header_false TEST HEADER) as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst
  end.
  - match goal with STOP : out_break_or_return _ _ |- _ => inversion STOP; subst end; repeat split; reflexivity.
  - match goal with BAD : out_normal_or_continue Out_break |- _ => inversion BAD end.
  - match goal with BAD : out_normal_or_continue Out_break |- _ => inversion BAD end.
Qed.

Lemma memory_long_iteration_encode fe ge locals temps memory iterator condition body value body_temps body_memory final_temps final :
  expression_test condition (Entry ge locals temps memory) true ->
  body_temps ! iterator = Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory body E0 body_temps body_memory Out_normal ->
  exec_stmt fe ge locals (PTree.set iterator (Vlong (Int64.repr (value+1))) body_temps) body_memory
    (memory_long_frontend_loop iterator condition body) E0 final_temps final Out_normal ->
  exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body) E0 final_temps final Out_normal.
Proof.
  intros [test [EVAL BOOL]] VALUE BODY REST; unfold memory_long_frontend_loop in *.
  eapply exec_Sloop_loop with (out1:=Out_normal) (t1:=E0) (t2:=E0) (t3:=E0).
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [|exact BODY].
    eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|constructor].
  - constructor.
  - apply memory_long_increment_execution; exact VALUE.
  - exact REST.
Qed.

Lemma memory_long_iteration_decode fe ge locals temps memory iterator condition body value final_temps final :
  expression_test condition (Entry ge locals temps memory) true ->
  temps ! iterator = Some (Vlong (Int64.repr value)) ->
  (forall le m tr le' m' out, exec_stmt fe ge locals le m body tr le' m' out -> out=Out_normal) ->
  (forall le m tr le' m', exec_stmt fe ge locals le m body tr le' m' Out_normal -> le' ! iterator = le ! iterator) ->
  exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body) E0 final_temps final Out_normal ->
  exists body_temps body_memory,
    exec_stmt fe ge locals temps memory body E0 body_temps body_memory Out_normal /\
    exec_stmt fe ge locals (PTree.set iterator (Vlong (Int64.repr (value+1))) body_temps) body_memory
      (memory_long_frontend_loop iterator condition body) E0 final_temps final Out_normal.
Proof.
  intros TEST VALUE NORMAL FRAME RUN; inversion RUN; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Ssequence (Sifthenelse _ _ _) _) _ _ _ _ |- _ =>
    pose proof (memory_long_header_true TEST HEADER) as BODY;
    pose proof (NORMAL _ _ _ _ _ _ BODY) as OUTCOME; subst
  end.
  - match goal with BAD : out_break_or_return Out_normal _ |- _ => inversion BAD end.
  - match goal with BODY : exec_stmt _ _ _ _ _ body _ ?le ?m Out_normal,
      INC : exec_stmt _ _ _ _ _ (memory_long_increment iterator) _ _ _ _ |- _ =>
    assert (IT : le ! iterator = Some (Vlong (Int64.repr value))) by (rewrite (FRAME _ _ _ _ _ BODY); exact VALUE);
    pose proof (memory_long_increment_exact IT INC) as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst
    end.
    match goal with BAD : out_break_or_return Out_normal _ |- _ => inversion BAD end.
  - match goal with BODY : exec_stmt _ _ _ _ _ body _ ?le ?m Out_normal,
      INC : exec_stmt _ _ _ _ _ (memory_long_increment iterator) _ _ _ _ |- _ =>
    assert (IT : le ! iterator = Some (Vlong (Int64.repr value))) by (rewrite (FRAME _ _ _ _ _ BODY); exact VALUE);
    pose proof (memory_long_increment_exact IT INC) as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst
    end.
    match goal with EMPTY : _ ** _ ** _ = E0 |- _ =>
      apply Eapp_E0_inv in EMPTY as [FIRST REST]; apply Eapp_E0_inv in REST as [SECOND THIRD]; subst
    end.
    do 2 eexists; split; eassumption.
Qed.

Print Assumptions memory_long_increment_exact.
Print Assumptions memory_long_header_decode.
Print Assumptions memory_long_loop_stop_decode.
Print Assumptions memory_long_iteration_encode.
Print Assumptions memory_long_iteration_decode.
