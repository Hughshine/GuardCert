From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint
  ClightProjectedExecution ClightLoopSyntax ClightRegionProgress ClightNoWrap ClightRedundantSet.
From GuardInterface Require Import ClightSignedExpressionProgress ClightStrictLoopProgress
  ClightStrictIteration ClightStableLoopCondition ClightQuietDeterminacy ClightCheckPlanFrame ClightAffineFirstBodyReceipt.
Import ListNotations.
Set Implicit Arguments.

(** The language supplies this bridge for a signed expression header. The
    captured word is the result of the entire bound expression, not a value
    loaded from an arbitrarily selected observation. *)
Lemma signed_expression_test_facts ge locals temps memory iterator bound flag :
  typeof bound = type_int32s ->
  expression_test (signed_expression_test iterator bound) (Entry ge locals temps memory) flag ->
  exists counter upper, temps!iterator=Some(Vint counter) /\
    eval_expr ge locals temps memory bound (Vint upper) /\ flag=Int.lt counter upper.
Proof.
  intros TYPE [result [EVAL BOOL]]; apply scalar_binary_inv in EVAL.
  destruct EVAL as [counter [upper [ROW [BOUND OP]]]]; apply scalar_temp_inv in ROW.
  unfold Cop.sem_binary_operation in OP; cbn [typeof] in OP; rewrite TYPE in OP.
  destruct counter; destruct upper; try discriminate OP.
  change (Some (Val.of_bool (Int.lt i i0)) = Some result) in OP.
  injection OP as VALUE; subst result; rewrite bool_of_bool in BOOL.
  exists i,i0; repeat split; try assumption; congruence.
Qed.

Lemma signed_expression_test_eval ge locals temps memory iterator bound counter upper :
  typeof bound = type_int32s -> temps!iterator=Some(Vint counter) ->
  eval_expr ge locals temps memory bound (Vint upper) ->
  expression_test (signed_expression_test iterator bound) (Entry ge locals temps memory) (Int.lt counter upper).
Proof.
  intros TYPE ROW BOUND; exists (Val.of_bool (Int.lt counter upper)); split; [|apply bool_of_bool].
  eapply eval_Ebinop; [apply eval_Etempvar; exact ROW|exact BOUND|].
  unfold Cop.sem_binary_operation; cbn [typeof]; rewrite TYPE; reflexivity.
Qed.

Lemma signed_expression_completed_header fe ge locals temps memory iterator bound body trace after final outcome :
  exec_stmt fe ge locals temps memory
    (strict_frontend_loop iterator (signed_expression_test iterator bound) body) trace after final outcome ->
  exists flag, expression_test (signed_expression_test iterator bound) (Entry ge locals temps memory) flag.
Proof.
  unfold strict_frontend_loop; intro SOURCE; inversion SOURCE; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _
    (Ssequence (Ssequence Sskip (Sifthenelse _ _ _)) _) _ _ _ _ |- _ =>
      destruct (strict_header_execution HEADER) as [flag [TEST _]]; exists flag; exact TEST end.
Qed.

Lemma signed_expression_bound_in_scope iterator bound body :
  incl (expression_temps bound)
    (statement_temps (strict_frontend_loop iterator (signed_expression_test iterator bound) body)).
Proof.
  unfold strict_frontend_loop,signed_expression_test; cbn [statement_temps expression_temps].
  intros id MEMBER; repeat rewrite in_app_iff; cbn; tauto.
Qed.

Theorem signed_expression_first_body_receipt fe ge locals temps memory iterator bound cache body after final upper :
  typeof bound=type_int32s -> normal_statement body=true -> quiet_statement body=true ->
  eval_expr ge locals temps memory bound (Vint upper) -> temps!cache=Some(Vint upper) ->
  exec_stmt fe ge locals temps memory
    (strict_frontend_loop iterator (signed_expression_test iterator bound) body) E0 after final Out_normal ->
  affine_first_body_receipt iterator cache body fe (Entry ge locals temps memory).
Proof.
  intros TYPE NORMAL QUIET EVAL CACHE SOURCE.
  destruct (signed_expression_completed_header SOURCE) as [flag TEST].
  destruct (@signed_expression_test_facts _ _ _ _ _ _ _ TYPE TEST)
    as [counter [word [ROW [BOUND FLAG]]]].
  pose proof (proj1(expressions_determinate ge locals temps memory) _ _ BOUND _ EVAL) as SAME.
  injection SAME as WORD; subst word.
  unfold affine_first_body_receipt; cbn [entry_temps register_domain].
  split; [exists counter; exact ROW|split; [exists upper; exact CACHE|]].
  intro ACTIVE; unfold temp_word in ACTIVE; rewrite ROW,CACHE in ACTIVE.
  assert (TRUE : flag=true).
  { rewrite FLAG; unfold Int.lt; destruct (zlt (Int.signed counter) (Int.signed upper));
      [reflexivity|contradiction]. }
  rewrite TRUE in TEST.
  destruct (@strict_active_iteration fe ge locals iterator (signed_expression_test iterator bound) body
    temps memory after final NORMAL QUIET TEST SOURCE)
    as [body_after [body_final [next [next_memory [BODY REST]]]]].
  exists body_after,body_final; exact BODY.
Qed.

(** A completed original source licenses the first evaluation, even when its
    first comparison is false. This step asserts no future read stability.
    The fallback source keeps its original compound header. *)
Theorem signed_expression_capture_receipt fe ge locals temps memory iterator bound body cache live after final :
  typeof bound=type_int32s -> normal_statement body=true -> quiet_statement body=true ->
  check_plan_frameable (strict_frontend_loop iterator (signed_expression_test iterator bound) body)=true ->
  ~In cache (statement_temps (strict_frontend_loop iterator (signed_expression_test iterator bound) body)++live) ->
  exec_stmt fe ge locals temps memory
    (strict_frontend_loop iterator (signed_expression_test iterator bound) body) E0 after final Out_normal ->
  exists upper prepared_after,
    exec_stmt fe ge locals temps memory (Sset cache bound)
      E0 (PTree.set cache (Vint upper) temps) memory Out_normal /\
    exec_stmt fe ge locals (PTree.set cache (Vint upper) temps) memory
      (strict_frontend_loop iterator (signed_expression_test iterator bound) body)
      E0 prepared_after final Out_normal /\
    temp_agree (statement_temps (strict_frontend_loop iterator (signed_expression_test iterator bound) body)++live)
      after prepared_after /\
    affine_first_body_receipt iterator cache body fe (Entry ge locals (PTree.set cache (Vint upper) temps) memory) /\
    eval_expr ge locals temps memory bound (Vint upper).
Proof.
  intros TYPE NORMAL QUIET FRAMEABLE PRIVATE SOURCE.
  destruct (signed_expression_completed_header SOURCE) as [flag TEST].
  destruct (@signed_expression_test_facts _ _ _ _ _ _ _ TYPE TEST) as [counter [upper [ROW [EVAL FLAG]]]].
  pose (scope := statement_temps (strict_frontend_loop iterator (signed_expression_test iterator bound) body)++live).
  assert (FRAME : temp_agree scope temps (PTree.set cache (Vint upper) temps)) by (apply temp_agree_set; exact PRIVATE).
  destruct (@structured_execution_temp_transport fe ge locals temps memory _ E0 after final Out_normal SOURCE
    scope (PTree.set cache (Vint upper) temps) (statement_temps _)
    (@check_plan_frameable_writes _ FRAMEABLE)
    ltac:(unfold statement_scope,scope; intros id MEMBER; apply in_or_app; left; exact MEMBER) FRAME)
    as [prepared_after [PREPARED PUBLIC]].
  exists upper,prepared_after; split; [constructor; exact EVAL|split; [exact PREPARED|split; [exact PUBLIC|split; [|exact EVAL]]]].
  eapply signed_expression_first_body_receipt; [exact TYPE|exact NORMAL|exact QUIET| |apply PTree.gss|exact PREPARED].
  eapply expression_temp_transport; [|exact FRAME|exact EVAL].
  unfold expression_scope,scope; intros id MEMBER; apply in_or_app; left; apply signed_expression_bound_in_scope; exact MEMBER.
Qed.

Print Assumptions signed_expression_test_facts.
Print Assumptions signed_expression_test_eval.
Print Assumptions signed_expression_completed_header.
Print Assumptions signed_expression_bound_in_scope.
Print Assumptions signed_expression_first_body_receipt.
Print Assumptions signed_expression_capture_receipt.

Lemma signed_expression_zero_trip_execution fe ge locals temps memory iterator bound body :
  expression_test (signed_expression_test iterator bound) (Entry ge locals temps memory) false ->
  exec_stmt fe ge locals temps memory
    (strict_frontend_loop iterator (signed_expression_test iterator bound) body) E0 temps memory Out_normal.
Proof.
  intros [value [EVAL BOOL]]; unfold strict_frontend_loop.
  eapply exec_Sloop_stop1 with (out':=Out_break).
  - eapply exec_Sseq_2; [|discriminate].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor|].
    eapply exec_Sifthenelse with (b:=false); [exact EVAL|exact BOOL|constructor].
  - constructor.
Qed.
Print Assumptions signed_expression_zero_trip_execution.
