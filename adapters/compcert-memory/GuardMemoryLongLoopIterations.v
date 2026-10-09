From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryLongLoopControl.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Retain all body temporaries, including the last inner-loop counters. Only
    the current iterator receives its actual I64 increment after the body. *)
Definition memory_long_iteration fe ge locals iterator body value
  (before after : temp_env*mem) := exists body_temps,
  exec_stmt fe ge locals (fst before) (snd before) body E0 body_temps (snd after) Out_normal /\
  fst after=PTree.set iterator (Vlong (Int64.repr (value+1))) body_temps.

Section FINITE_LONG_LOOP.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable iterator : ident.
Variable condition : expr.
Variable body : statement.
Variable upper floor : Z.
Variable invariant : temp_env -> mem -> Prop.
Hypothesis HEADER : forall temps memory value, invariant temps memory ->
  floor<=value<=upper -> temps ! iterator=Some (Vlong (Int64.repr value)) ->
  expression_test condition (Entry ge locals temps memory) (value <? upper).
Hypothesis NORMAL : forall temps memory trace after final outcome,
  exec_stmt fe ge locals temps memory body trace after final outcome -> outcome=Out_normal.
Hypothesis FRAME : forall temps memory trace after final,
  exec_stmt fe ge locals temps memory body trace after final Out_normal -> after ! iterator=temps ! iterator.
Hypothesis BODY_INV : forall temps memory value after final,
  invariant temps memory -> floor<=value<upper -> temps ! iterator=Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal -> invariant after final.
Hypothesis INCREMENT_INV : forall temps memory value,
  invariant temps memory -> invariant (PTree.set iterator (Vlong (Int64.repr (value+1))) temps) memory.

Theorem memory_long_counted_loop_encode count : forall value temps memory after final,
  upper=value+Z.of_nat count -> floor<=value -> invariant temps memory ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  counted_iterations (memory_long_iteration fe ge locals iterator body) count value
    (temps,memory) (after,final) ->
  exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body) E0 after final Out_normal.
Proof.
  induction count as [|count IH]; intros value temps memory after final LENGTH LOWER INV VALUE ITER.
  - assert (SAME : value=upper) by (cbn in LENGTH; lia); subst value.
    inversion ITER; subst after final.
    apply memory_long_loop_stop_execution; pose proof (@HEADER temps memory upper INV ltac:(lia) VALUE) as TEST.
    rewrite Z.ltb_irrefl in TEST; exact TEST.
  - rewrite Nat2Z.inj_succ in LENGTH.
    inversion ITER as [|n x first middle last POINT REST]; subst n x first last.
    destruct middle as [middle_temps middle_memory].
    destruct POINT as [body_temps [BODY TEMPS]]; cbn in BODY,TEMPS; subst middle_temps.
    assert (LT : value<upper) by (pose proof (Nat2Z.is_nonneg count); lia).
    assert (BODY_VALUE : body_temps ! iterator=Some (Vlong (Int64.repr value)))
      by (rewrite (@FRAME _ _ _ _ _ BODY); exact VALUE).
    assert (NEXT_INV : invariant (PTree.set iterator (Vlong (Int64.repr (value+1))) body_temps) middle_memory).
    { apply INCREMENT_INV; exact (@BODY_INV temps memory value body_temps middle_memory INV ltac:(lia) VALUE BODY). }
    assert (TEST : expression_test condition (Entry ge locals temps memory) true).
    { pose proof (@HEADER temps memory value INV ltac:(lia) VALUE) as TEST;
      rewrite (proj2 (Z.ltb_lt value upper) LT) in TEST; exact TEST. }
    eapply memory_long_iteration_encode; [exact TEST|exact BODY_VALUE|exact BODY|].
    eapply IH with (value:=value+1); [lia|lia|exact NEXT_INV|apply PTree.gss|exact REST].
Qed.

Theorem memory_long_counted_loop_decode count : forall value temps memory after final,
  upper=value+Z.of_nat count -> floor<=value -> invariant temps memory ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body) E0 after final Out_normal ->
  counted_iterations (memory_long_iteration fe ge locals iterator body) count value
    (temps,memory) (after,final).
Proof.
  induction count as [|count IH]; intros value temps memory after final LENGTH LOWER INV VALUE RUN.
  - assert (SAME : value=upper) by (cbn in LENGTH; lia); subst value.
    pose proof (@HEADER temps memory upper INV ltac:(lia) VALUE) as TEST; rewrite Z.ltb_irrefl in TEST.
    destruct (memory_long_loop_stop_decode TEST RUN) as [_ [TEMPS [MEMORY _]]]; subst after final; constructor.
  - rewrite Nat2Z.inj_succ in LENGTH.
    assert (LT : value<upper) by (pose proof (Nat2Z.is_nonneg count); lia).
    assert (TEST : expression_test condition (Entry ge locals temps memory) true).
    { pose proof (@HEADER temps memory value INV ltac:(lia) VALUE) as TEST;
      rewrite (proj2 (Z.ltb_lt value upper) LT) in TEST; exact TEST. }
    destruct (@memory_long_iteration_decode fe ge locals temps memory iterator condition body value after final
      TEST VALUE NORMAL FRAME RUN) as [body_temps [body_memory [BODY REST]]].
    eapply iterations_next with (s1:=(PTree.set iterator (Vlong (Int64.repr (value+1))) body_temps,body_memory)).
    + exists body_temps; split; [exact BODY|reflexivity].
    + eapply IH with (value:=value+1); [lia|lia| |apply PTree.gss|exact REST].
      apply INCREMENT_INV; exact (@BODY_INV temps memory value body_temps body_memory INV ltac:(lia) VALUE BODY).
Qed.

Theorem memory_long_counted_loop_equivalence count value temps memory after final :
  upper=value+Z.of_nat count -> floor<=value -> invariant temps memory ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  (exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body) E0 after final Out_normal <->
   counted_iterations (memory_long_iteration fe ge locals iterator body) count value (temps,memory) (after,final)).
Proof.
  intros LENGTH LOWER INV VALUE; split.
  - apply memory_long_counted_loop_decode; assumption.
  - apply memory_long_counted_loop_encode; assumption.
Qed.
End FINITE_LONG_LOOP.

Print Assumptions memory_long_counted_loop_encode.
Print Assumptions memory_long_counted_loop_decode.
Print Assumptions memory_long_counted_loop_equivalence.
