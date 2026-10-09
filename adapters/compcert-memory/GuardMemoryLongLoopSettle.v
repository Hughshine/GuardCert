From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryDoubleMatmulLoops.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_long_settled_exit iterator (settle : Z -> temp_env -> temp_env) count value temps :=
  match count with
  | O => temps
  | S rest => memory_long_settled_exit iterator settle rest (value+1)
      (PTree.set iterator (Vlong (Int64.repr (value+1))) (settle value temps)) end.

Section SETTLED_LOOP.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable iterator : ident.
Variable condition : expr.
Variable body : statement.
Variable upper floor : Z.
Variable invariant : temp_env -> mem -> Prop.
Variable physical : Z -> mem -> mem -> Prop.
Variable settle : Z -> temp_env -> temp_env.
Hypothesis HEADER : forall temps memory value, invariant temps memory -> floor<=value<=upper ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  expression_test condition (Entry ge locals temps memory) (value <? upper).
Hypothesis NORMAL : forall le m tr le' m' out, exec_stmt fe ge locals le m body tr le' m' out -> out=Out_normal.
Hypothesis FRAME : forall le m tr le' m', exec_stmt fe ge locals le m body tr le' m' Out_normal ->
  le' ! iterator=le ! iterator.
Hypothesis BRIDGE : forall value temps memory after final,
  floor<=value<upper -> invariant temps memory -> temps ! iterator=Some (Vlong (Int64.repr value)) ->
  (exec_stmt fe ge locals temps memory body E0 after final Out_normal <->
   physical value memory final /\ after=settle value temps).
Hypothesis BODY_INV : forall value temps memory after final,
  floor<=value<upper -> invariant temps memory -> temps ! iterator=Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal -> invariant after final.
Hypothesis SET_INV : forall temps memory value, invariant temps memory ->
  invariant (PTree.set iterator (Vlong (Int64.repr value)) temps) memory.

Theorem memory_long_settled_decode count : forall value temps memory after final,
  upper=value+Z.of_nat count -> floor<=value -> invariant temps memory ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body) E0 after final Out_normal ->
  counted_iterations physical count value memory final /\
  after=memory_long_settled_exit iterator settle count value temps.
Proof.
  induction count as [|count IH]; intros value temps memory after final LENGTH LOWER INV VALUE RUN.
  - assert (SAME : value=upper) by (cbn in LENGTH; lia); subst value.
    pose proof (@HEADER temps memory upper INV ltac:(lia) VALUE) as TEST; rewrite Z.ltb_irrefl in TEST.
    destruct (memory_long_loop_stop_decode TEST RUN) as [_ [TEMPS [MEMORY _]]]; subst after final;
      split; [constructor|reflexivity].
  - rewrite Nat2Z.inj_succ in LENGTH; assert (LT : value<upper) by (pose proof (Nat2Z.is_nonneg count); lia).
    pose proof (@HEADER temps memory value INV ltac:(lia) VALUE) as TEST;
      rewrite (proj2 (Z.ltb_lt value upper) LT) in TEST.
    destruct (@memory_long_iteration_decode fe ge locals temps memory iterator condition body value after final
      TEST VALUE NORMAL FRAME RUN) as [body_temps [body_memory [BODY REST]]].
    destruct (proj1 (@BRIDGE value temps memory body_temps body_memory ltac:(lia) INV VALUE) BODY) as [ACTION EXIT].
    assert (NEXT : invariant (PTree.set iterator (Vlong (Int64.repr (value+1))) body_temps) body_memory).
    { apply SET_INV; exact (@BODY_INV value temps memory body_temps body_memory ltac:(lia) INV VALUE BODY). }
    destruct (@IH (value+1) _ body_memory after final ltac:(lia) ltac:(lia) NEXT (PTree.gss _ _ _) REST) as [ITER LAST].
    split; [eapply iterations_next; eauto|cbn [memory_long_settled_exit]; rewrite <- EXIT; exact LAST].
Qed.

Theorem memory_long_settled_encode count : forall value temps memory final,
  upper=value+Z.of_nat count -> floor<=value -> invariant temps memory ->
  temps ! iterator=Some (Vlong (Int64.repr value)) -> counted_iterations physical count value memory final ->
  exec_stmt fe ge locals temps memory (memory_long_frontend_loop iterator condition body) E0
    (memory_long_settled_exit iterator settle count value temps) final Out_normal.
Proof.
  induction count as [|count IH]; intros value temps memory final LENGTH LOWER INV VALUE ITER.
  - inversion ITER; subst final.
    apply memory_long_loop_stop_execution; pose proof (@HEADER temps memory value INV ltac:(cbn in LENGTH; lia) VALUE) as TEST.
    assert (FALSE : (value <? upper)=false) by (apply Z.ltb_ge; cbn in LENGTH; lia); rewrite FALSE in TEST; exact TEST.
  - rewrite Nat2Z.inj_succ in LENGTH; assert (LT : value<upper) by (pose proof (Nat2Z.is_nonneg count); lia).
    inversion ITER as [|n x first middle last ACTION REST]; subst n x first last.
    assert (BODY : exec_stmt fe ge locals temps memory body E0 (settle value temps) middle Out_normal).
    { apply (proj2 (@BRIDGE value temps memory (settle value temps) middle ltac:(lia) INV VALUE)); auto. }
    assert (BODY_VALUE : (settle value temps) ! iterator=Some (Vlong (Int64.repr value)))
      by (rewrite (@FRAME _ _ _ _ _ BODY); exact VALUE).
    assert (NEXT : invariant (PTree.set iterator (Vlong (Int64.repr (value+1))) (settle value temps)) middle).
    { apply SET_INV; exact (@BODY_INV value temps memory (settle value temps) middle ltac:(lia) INV VALUE BODY). }
    pose proof (@HEADER temps memory value INV ltac:(lia) VALUE) as TEST;
      rewrite (proj2 (Z.ltb_lt value upper) LT) in TEST.
    cbn [memory_long_settled_exit]; eapply memory_long_iteration_encode; [exact TEST|exact BODY_VALUE|exact BODY|].
    eapply IH with (value:=value+1); [lia|lia|exact NEXT|apply PTree.gss|exact REST].
Qed.

Theorem memory_long_initialized_settled_equivalence count temps memory after final :
  upper=Z.of_nat count -> floor<=0 -> invariant temps memory ->
  (exec_stmt fe ge locals temps memory (memory_long_initialized_loop iterator condition body) E0 after final Out_normal <->
   counted_iterations physical count 0 memory final /\
   after=memory_long_settled_exit iterator settle count 0 (PTree.set iterator (Vlong Int64.zero) temps)).
Proof.
  intros LENGTH LOWER INV; split.
  - intro RUN; apply memory_long_initialized_decode in RUN.
    eapply memory_long_settled_decode; [lia|exact LOWER|apply SET_INV; exact INV|apply PTree.gss|exact RUN].
  - intros [ITER EXIT]; subst after; unfold memory_long_initialized_loop.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [apply memory_long_initialization_execution|].
    eapply memory_long_settled_encode; [lia|exact LOWER|apply SET_INV; exact INV|apply PTree.gss|exact ITER].
Qed.
End SETTLED_LOOP.

Lemma memory_long_constant_settle_exit iterator (settle : temp_env -> temp_env)
  (IDEMPOTENT : forall temps, settle (settle temps)=settle temps)
  (COMMUTE : forall temps word, settle (PTree.set iterator word temps)=PTree.set iterator word (settle temps)) :
  forall count value temps,
  memory_long_settled_exit iterator (fun _ => settle) (S count) value temps=
  PTree.set iterator (Vlong (Int64.repr (value+Z.of_nat (S count)))) (settle temps).
Proof.
  induction count as [|count IH]; intros value temps.
  - cbn [memory_long_settled_exit]; replace (value+Z.of_nat 1) with (value+1) by reflexivity; reflexivity.
  - change (memory_long_settled_exit iterator (fun _ => settle) (S count) (value+1)
      (PTree.set iterator (Vlong (Int64.repr (value+1))) (settle temps)) =
      PTree.set iterator (Vlong (Int64.repr (value+Z.of_nat (S (S count))))) (settle temps)).
    rewrite IH,COMMUTE,IDEMPOTENT,PTree.set2.
    assert (SAME : value+1+Z.of_nat (S count)=value+Z.of_nat (S (S count)))
      by (rewrite !Nat2Z.inj_succ; lia).
    rewrite SAME; reflexivity.
Qed.

Print Assumptions memory_long_settled_decode.
Print Assumptions memory_long_settled_encode.
Print Assumptions memory_long_initialized_settled_equivalence.
Print Assumptions memory_long_constant_settle_exit.
