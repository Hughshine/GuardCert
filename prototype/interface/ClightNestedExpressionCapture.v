From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint
  ClightProjectedExecution ClightLoopSyntax ClightRegionProgress ClightStraightLine
  ClightRectangularLoops ClightNoWrap ClightCountedLoop.
From GuardInterface Require Import ClightSignedExpressionProgress ClightStrictLoopProgress
  ClightStrictIteration ClightExpressionHeaderCapture ClightCheckPlanFrame ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.

Definition nested_expression_body column child_bound body :=
  Ssequence (rectangle_reset column)
    (strict_frontend_loop column (signed_expression_test column child_bound) body).
Definition nested_expression_source row bound column child_bound body :=
  strict_frontend_loop row (signed_expression_test row bound)
    (nested_expression_body column child_bound body).

(** The second capture is guarded by the actual first comparison. In
    particular, an inactive outer loop does not evaluate the child bound. *)
Definition nested_expression_capture row cache bound child_cache child_bound :=
  Ssequence (Sset cache bound)
    (Sifthenelse (signed_expression_test row (Etempvar cache type_int32s))
      (Sset child_cache child_bound) Sskip).
Definition nested_expression_captured cache child_cache temps upper child :=
  match child with
  | Some word => PTree.set child_cache (Vint word) (PTree.set cache (Vint upper) temps)
  | None => PTree.set cache (Vint upper) temps
  end.

Lemma nested_expression_captured_frame scope cache child_cache temps upper child :
  ~In cache scope -> ~In child_cache scope ->
  temp_agree scope temps (nested_expression_captured cache child_cache temps upper child).
Proof.
  intros PRIVATE CHILD_PRIVATE; unfold nested_expression_captured; destruct child.
  - eapply temp_agree_trans; apply temp_agree_set; eassumption.
  - apply temp_agree_set; exact PRIVATE.
Qed.
Lemma nested_expression_captured_root cache child_cache temps upper child :
  cache<>child_cache ->
  (nested_expression_captured cache child_cache temps upper child)!cache=Some(Vint upper).
Proof. intro DISTINCT; unfold nested_expression_captured; destruct child; [rewrite PTree.gso by exact DISTINCT|]; apply PTree.gss. Qed.
Lemma nested_expression_captured_child cache child_cache temps upper child_word :
  (nested_expression_captured cache child_cache temps upper (Some child_word))!child_cache=Some(Vint child_word).
Proof. apply PTree.gss. Qed.

Lemma nested_expression_body_normal column bound body :
  quiet_statement body=true -> normal_statement (nested_expression_body column bound body)=true.
Proof. intro QUIET; cbn [nested_expression_body rectangle_reset strict_frontend_loop normal_statement quiet_statement counter_increment]; rewrite QUIET; reflexivity. Qed.
Lemma nested_expression_body_quiet column bound body :
  quiet_statement body=true -> quiet_statement (nested_expression_body column bound body)=true.
Proof. intro QUIET; cbn [nested_expression_body rectangle_reset strict_frontend_loop quiet_statement counter_increment]; rewrite QUIET; reflexivity. Qed.

(** This witness is an execution of the original child at its reached reset
    state, in the original memory. It does not require a cached child. *)
Lemma nested_expression_first_child fe ge locals temps memory row bound column child_bound body after final upper :
  typeof bound=type_int32s -> quiet_statement body=true ->
  eval_expr ge locals temps memory bound (Vint upper) ->
  Int.lt (temp_word row temps) upper=true ->
  exec_stmt fe ge locals temps memory (nested_expression_source row bound column child_bound body)
    E0 after final Out_normal ->
  exists child_after child_final,
    exec_stmt fe ge locals (PTree.set column (Vint Int.zero) temps) memory
      (strict_frontend_loop column (signed_expression_test column child_bound) body)
      E0 child_after child_final Out_normal.
Proof.
  intros TYPE QUIET EVAL ACTIVE SOURCE.
  destruct (signed_expression_completed_header SOURCE) as [flag TEST].
  destruct (@signed_expression_test_facts _ _ _ _ _ _ _ TYPE TEST)
    as [counter [word [ROW [BOUND FLAG]]]].
  pose proof (proj1(expressions_determinate ge locals temps memory) _ _ BOUND _ EVAL) as SAME.
  injection SAME as WORD; subst word.
  unfold temp_word in ACTIVE; rewrite ROW in ACTIVE; rewrite FLAG,ACTIVE in TEST.
  destruct (@strict_active_iteration fe ge locals row (signed_expression_test row bound)
    (nested_expression_body column child_bound body) temps memory after final
    (@nested_expression_body_normal column child_bound body QUIET)
    (@nested_expression_body_quiet column child_bound body QUIET) TEST SOURCE)
    as [body_after [body_final [next [next_memory [BODY REST]]]]].
  destruct (sequence_normal_decode BODY) as [reset [reset_memory [RESET CHILD]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  exists body_after,body_final; exact CHILD.
Qed.

Theorem nested_expression_capture_execution fe ge locals temps memory row bound column child_bound body
  cache child_cache live after final :
  typeof bound=type_int32s -> typeof child_bound=type_int32s -> quiet_statement body=true ->
  check_plan_frameable (nested_expression_source row bound column child_bound body)=true ->
  ~In cache (statement_temps (nested_expression_source row bound column child_bound body)++live) ->
  ~In child_cache (statement_temps (nested_expression_source row bound column child_bound body)++live) ->
  cache<>child_cache -> ~In column (expression_temps child_bound) ->
  exec_stmt fe ge locals temps memory (nested_expression_source row bound column child_bound body)
    E0 after final Out_normal ->
  exists upper child prepared_after,
    exec_stmt fe ge locals temps memory (nested_expression_capture row cache bound child_cache child_bound)
      E0 (nested_expression_captured cache child_cache temps upper child) memory Out_normal /\
    exec_stmt fe ge locals (nested_expression_captured cache child_cache temps upper child) memory
      (nested_expression_source row bound column child_bound body) E0 prepared_after final Out_normal /\
    temp_agree (statement_temps (nested_expression_source row bound column child_bound body)++live)
      after prepared_after /\
    eval_expr ge locals temps memory bound (Vint upper) /\
    (match child with
    | None => Int.lt (temp_word row temps) upper=false
    | Some word => Int.lt (temp_word row temps) upper=true /\
        eval_expr ge locals temps memory child_bound (Vint word)
    end).
Proof.
  intros TYPE CHILD_TYPE QUIET FRAMEABLE PRIVATE CHILD_PRIVATE DISTINCT CHILD_INDEPENDENT SOURCE.
  pose (source := nested_expression_source row bound column child_bound body).
  pose (scope := statement_temps source++live).
  destruct (@signed_expression_capture_receipt fe ge locals temps memory row bound
    (nested_expression_body column child_bound body) cache live after final TYPE
    (@nested_expression_body_normal column child_bound body QUIET)
    (@nested_expression_body_quiet column child_bound body QUIET) FRAMEABLE PRIVATE SOURCE)
    as [upper [root_after [ROOT_CAPTURE [PREPARED [PUBLIC [RECEIPT EVAL]]]]]].
  assert (ROW_SCOPE : In row scope).
  { unfold scope,source,nested_expression_source,strict_frontend_loop,signed_expression_test;
      cbn [statement_temps expression_temps]; repeat rewrite in_app_iff; cbn; tauto. }
  assert (ROOT_FRAME : temp_agree scope temps (PTree.set cache (Vint upper) temps)).
  { apply temp_agree_set; exact PRIVATE. }
  assert (ROOT_ROW : (PTree.set cache (Vint upper) temps)!row=temps!row) by (apply ROOT_FRAME; exact ROW_SCOPE).
  destruct (signed_expression_completed_header SOURCE) as [flag TEST].
  destruct (@signed_expression_test_facts _ _ _ _ _ _ _ TYPE TEST)
    as [counter [word [ROW [BOUND FLAG]]]].
  pose proof (proj1(expressions_determinate ge locals temps memory) _ _ BOUND _ EVAL) as SAME.
  injection SAME as WORD; subst word.
  assert (COUNTER : temp_word row temps=counter) by (unfold temp_word; rewrite ROW; reflexivity).
  assert (ROOT_TEST : expression_test (signed_expression_test row (Etempvar cache type_int32s))
    (Entry ge locals (PTree.set cache (Vint upper) temps) memory) (Int.lt counter upper)).
  { apply signed_expression_test_eval; [reflexivity|rewrite ROOT_ROW; exact ROW|apply eval_Etempvar,PTree.gss]. }
  destruct (Int.lt counter upper) eqn:ACTIVE.
  - destruct (@nested_expression_first_child fe ge locals temps memory row bound column child_bound body
      after final upper TYPE QUIET EVAL ltac:(rewrite COUNTER; exact ACTIVE) SOURCE)
      as [child_after [child_final CHILD]].
    destruct (signed_expression_completed_header CHILD) as [child_flag CHILD_TEST].
    destruct (@signed_expression_test_facts _ _ _ _ _ _ _ CHILD_TYPE CHILD_TEST)
      as [child_counter [child_word [CHILD_ROW [CHILD_EVAL CHILD_FLAG]]]].
    assert (CHILD_ENTRY_EVAL : eval_expr ge locals temps memory child_bound (Vint child_word)).
    { eapply expression_temp_transport; [unfold expression_scope; apply incl_refl| |exact CHILD_EVAL].
      intros id MEMBER; rewrite PTree.gso by (intro SAME; subst id; contradiction); reflexivity. }
    assert (CHILD_PREPARED_EVAL : eval_expr ge locals (PTree.set cache (Vint upper) temps) memory child_bound (Vint child_word)).
    { eapply expression_temp_transport; [|exact ROOT_FRAME|exact CHILD_ENTRY_EVAL].
      unfold expression_scope,scope,source,nested_expression_source,nested_expression_body,strict_frontend_loop,signed_expression_test;
        cbn [statement_temps expression_temps]; intros id MEMBER; repeat rewrite in_app_iff; cbn; tauto. }
    destruct (@structured_execution_temp_transport fe ge locals (PTree.set cache (Vint upper) temps) memory
      source E0 root_after final Out_normal PREPARED scope
      (PTree.set child_cache (Vint child_word) (PTree.set cache (Vint upper) temps))
      (statement_temps source) (@check_plan_frameable_writes source FRAMEABLE)
      ltac:(unfold statement_scope,scope; intros id MEMBER; apply in_or_app; left; exact MEMBER)
      (@temp_agree_set scope _ child_cache (Vint child_word) CHILD_PRIVATE)) as [prepared_after [PREPARED_CHILD CHILD_PUBLIC]].
    exists upper,(Some child_word),prepared_after.
    split; [|split; [exact PREPARED_CHILD|split; [eapply temp_agree_trans; eassumption|split; [exact EVAL|]]]].
    + unfold nested_expression_capture,nested_expression_captured.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact ROOT_CAPTURE|].
      destruct ROOT_TEST as [value [READ BOOL]]; eapply exec_Sifthenelse; [exact READ|exact BOOL|].
      constructor; exact CHILD_PREPARED_EVAL.
    + split; [rewrite COUNTER; exact ACTIVE|exact CHILD_ENTRY_EVAL].
  - exists upper,None,root_after.
    split; [|split; [exact PREPARED|split; [exact PUBLIC|split; [exact EVAL|rewrite COUNTER; exact ACTIVE]]]].
    unfold nested_expression_capture,nested_expression_captured.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact ROOT_CAPTURE|].
    destruct ROOT_TEST as [value [READ BOOL]]; eapply exec_Sifthenelse; [exact READ|exact BOOL|constructor].
Qed.

Print Assumptions nested_expression_body_normal.
Print Assumptions nested_expression_body_quiet.
Print Assumptions nested_expression_captured_frame.
Print Assumptions nested_expression_captured_root.
Print Assumptions nested_expression_captured_child.
Print Assumptions nested_expression_first_child.
Print Assumptions nested_expression_capture_execution.
