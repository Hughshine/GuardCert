From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightProjectedExecution
  ClightCountedLoop ClightFrontendLoopProtocol ClightLoopExecution ClightLoopSyntax ClightParametricLoops.
Set Implicit Arguments.
Import ListNotations.

(** A local iteration runs the actual body with the original entry's other
    temporaries and the current mathematical counter encoded as a machine int.
    The bridge checks source syntax/effects rather than inventing a detached
    operation list. Only memory-writing bodies are supported here. *)
Definition canonical_body_run fe ge locals body base iterator index before after :=
  let current := PTree.set iterator (Vint (Int.repr index)) base in
  exec_stmt fe ge locals current before body E0 current after Out_normal.

Theorem counted_body_decode fe ge locals iterator bound body base before after final count lower upper :
  iterator <> bound -> normal_statement body = true -> writes_only [] body ->
  signed_range lower -> signed_range upper -> upper = (lower + Z.of_nat count)%Z ->
  base ! iterator = Some (Vint (Int.repr lower)) -> base ! bound = Some (Vint (Int.repr upper)) ->
  exec_stmt fe ge locals base before (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
  counted_iterations (canonical_body_run fe ge locals body base iterator) count lower before final /\
  after = PTree.set iterator (Vint (Int.repr upper)) base.
Proof.
  intros DISTINCT NORMAL WRITES LOWER UPPER LENGTH ITER BOUND RUN.
  assert (RESULT : counted_iterations (canonical_body_run fe ge locals body base iterator) count lower before final /\
    after = loop_exit None iterator base count upper).
  { eapply (@frontend_parametric_decode fe ge locals iterator bound body None
      (canonical_body_run fe ge locals body base iterator) lower upper
      (temp_except (statement_temps body) iterator) base).
    - exact DISTINCT.
    - split; cbn; tauto.
    - apply temp_except_iterator.
    - intros id _ BAD; exact BAD.
    - exact NORMAL.
    - exact WRITES.
    - exact UPPER.
    - intros index current memory exit memory' _ I _ FRAME BODY.
      pose proof (@canonical_temp_agreement (statement_temps body) iterator base current
        (Vint (Int.repr index)) I FRAME) as AGREE.
      destruct (@structured_execution_temp_transport fe ge locals current memory body E0 exit memory' Out_normal
        BODY (statement_temps body) (PTree.set iterator (Vint (Int.repr index)) base) [] WRITES
        (incl_refl _) (temp_agree_sym AGREE)) as [canonical_exit [EXEC _]].
      pose proof (memory_body_temporaries_exact WRITES EXEC) as CANONICAL; subst canonical_exit.
      split; [exact EXEC|exact (memory_body_temporaries_exact WRITES BODY)].
    - exact LENGTH.
    - exact LOWER.
    - apply Z.le_refl.
    - exact ITER.
    - exact BOUND.
    - apply temp_agree_refl.
    - exact RUN. }
  destruct RESULT as [POINTS EXIT]; split; [exact POINTS|].
  destruct count; exact EXIT.
Qed.

Theorem counted_body_encode fe ge locals iterator bound body base before final count lower upper :
  iterator <> bound -> writes_only [] body -> signed_range lower -> signed_range upper ->
  upper = (lower + Z.of_nat count)%Z ->
  base ! iterator = Some (Vint (Int.repr lower)) -> base ! bound = Some (Vint (Int.repr upper)) ->
  counted_iterations (canonical_body_run fe ge locals body base iterator) count lower before final ->
  exec_stmt fe ge locals base before (frontend_counted_loop iterator bound body) E0
    (PTree.set iterator (Vint (Int.repr upper)) base) final Out_normal.
Proof.
  intros DISTINCT WRITES LOWER UPPER LENGTH ITER BOUND POINTS.
  assert (RUN : exec_stmt fe ge locals base before (frontend_counted_loop iterator bound body) E0
    (loop_exit None iterator base count upper) final Out_normal).
  { eapply (@frontend_parametric_encode fe ge locals iterator bound body None
      (canonical_body_run fe ge locals body base iterator) lower upper
      (temp_except (statement_temps body) iterator) base).
    - exact DISTINCT.
    - split; cbn; tauto.
    - apply temp_except_iterator.
    - intros id _ BAD; exact BAD.
    - exact UPPER.
    - intros index current memory memory' _ I _ FRAME BODY.
      pose proof (@canonical_temp_agreement (statement_temps body) iterator base current
        (Vint (Int.repr index)) I FRAME) as AGREE.
      destruct (@structured_execution_temp_transport fe ge locals
        (PTree.set iterator (Vint (Int.repr index)) base) memory body E0
        (PTree.set iterator (Vint (Int.repr index)) base) memory' Out_normal
        BODY (statement_temps body) current [] WRITES (incl_refl _) AGREE) as [exit [EXEC _]].
      pose proof (memory_body_temporaries_exact WRITES EXEC) as SAME; subst exit; exact EXEC.
    - exact POINTS.
    - exact LENGTH.
    - exact LOWER.
    - apply Z.le_refl.
    - exact ITER.
    - exact BOUND.
    - apply temp_agree_refl. }
  destruct count; exact RUN.
Qed.

Print Assumptions counted_body_decode.
Print Assumptions counted_body_encode.
