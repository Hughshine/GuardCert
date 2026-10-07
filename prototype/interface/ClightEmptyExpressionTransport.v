From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFrontendLoopProtocol ClightLoopExecution ClightRegionProgress.
From GuardInterface Require Import ClightSignedExpressionProgress ClightStrictLoopProgress
  ClightExpressionHeaderCapture ClightQuietDeterminacy.
Set Implicit Arguments.

(** A refused first header executes no body, irrespective of its effects. *)
Lemma strict_false_execution fe ge locals temps memory iterator condition body :
  expression_test condition(Entry ge locals temps memory) false ->
  exec_stmt fe ge locals temps memory(strict_frontend_loop iterator condition body) E0 temps memory Out_normal.
Proof.
  intros [value [EVAL BOOL]]; unfold strict_frontend_loop.
  eapply exec_Sloop_stop1 with(out':=Out_break); [|constructor].
  eapply exec_Sseq_2 with(out:=Out_break); [|discriminate].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor|].
  eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
Qed.

(** Empty outer transport needs only its own header/cache. In particular this
    does not require a defined child cache, child expression, or body pointer. *)
Theorem expression_zero_cached_transport fe ge locals temps memory iterator cache bound body cached_body after final :
  typeof bound=type_int32s -> quiet_statement body=true ->
  temps!iterator=Some(Vint Int.zero) -> temps!cache=Some(Vint Int.zero) ->
  eval_expr ge locals temps memory bound(Vint Int.zero) ->
  exec_stmt fe ge locals temps memory(strict_frontend_loop iterator(signed_expression_test iterator bound) body)
    E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(frontend_counted_loop iterator cache cached_body) E0 after final Out_normal /\
  after=temps /\ final=memory.
Proof.
  intros TYPE QUIET ROW CACHE HEADER SOURCE.
  assert (TEST : expression_test(signed_expression_test iterator bound)(Entry ge locals temps memory) false).
  { change (expression_test(signed_expression_test iterator bound)(Entry ge locals temps memory)(Int.lt Int.zero Int.zero)).
    apply signed_expression_test_eval; assumption. }
  pose proof(@strict_false_execution fe ge locals temps memory iterator(signed_expression_test iterator bound) body TEST) as EMPTY.
  destruct(quiet_execution_determinate SOURCE
    ltac:(unfold strict_frontend_loop; cbn [quiet_statement]; rewrite QUIET; reflexivity) EMPTY)
    as [_ [TEMPS [MEMORY _]]]; subst after final.
  split; [|split; reflexivity].
  apply frontend_zero_trip_encode.
  exists(Vint Int.zero); split; [|reflexivity].
  eapply eval_Ebinop; [constructor; exact ROW|constructor; exact CACHE|reflexivity].
Qed.

Print Assumptions strict_false_execution.
Print Assumptions expression_zero_cached_transport.
