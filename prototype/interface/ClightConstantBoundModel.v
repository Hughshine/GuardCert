From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightCountedLoop
  ClightPureExpr ClightNoWrap ClightLoopSyntax ClightStraightLine ClightRectangularLoops ClightFrontendLoopProtocol
  ClightTempFootprint ClightProjectedExecution.
From GuardInterface Require Import ClightStrictLoopProgress ClightActiveLoopTransport
  ClightExpressionHeaderCapture ClightSignedExpressionProgress ClightNestedExpressionTransport ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.

Definition prepare_model_bounds cache child_helper component_helper upper :=
  Ssequence(Sset child_helper(Etempvar cache type_int32s))
    (Sset component_helper(Econst_int upper type_int32s)).
Definition prepared_model_temps temps child_helper component_helper child_upper upper :=
  PTree.set component_helper(Vint upper)(PTree.set child_helper(Vint child_upper)temps).

Theorem model_bounds_prepare_execution fe ge locals temps memory cache child_helper component_helper child_upper upper :
  temps!cache=Some(Vint child_upper) ->
  exec_stmt fe ge locals temps memory(prepare_model_bounds cache child_helper component_helper upper)
    E0(prepared_model_temps temps child_helper component_helper child_upper upper) memory Out_normal.
Proof.
  intro CHILD; unfold prepare_model_bounds,prepared_model_temps.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); constructor; constructor; auto.
Qed.

Lemma model_bounds_prepare_frame temps child_helper component_helper child_upper upper live :
  ~In child_helper live -> ~In component_helper live ->
  temp_agree live temps(prepared_model_temps temps child_helper component_helper child_upper upper).
Proof.
  intros CHILD COMPONENT; unfold prepared_model_temps.
  eapply temp_agree_trans; apply temp_agree_set; assumption.
Qed.

(** The actual preparation is allowed to initialize previously undefined
    helpers. Freshness against the original AST licenses transport of that
    same source, with its original memory and public exit observations. *)
Theorem model_bounds_prepare_source fe ge locals temps memory source after final live
  child_helper component_helper child_upper upper :
  check_plan_frameable source=true -> child_helper<>component_helper ->
  ~In child_helper(statement_temps source++live) ->
  ~In component_helper(statement_temps source++live) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists prepared_after,
    exec_stmt fe ge locals(prepared_model_temps temps child_helper component_helper child_upper upper)
      memory source E0 prepared_after final Out_normal /\
    temp_agree(statement_temps source++live) after prepared_after /\
    prepared_after!child_helper=Some(Vint child_upper) /\ prepared_after!component_helper=Some(Vint upper).
Proof.
  intros FRAMEABLE DISTINCT CHILD COMPONENT SOURCE.
  pose (scope:=statement_temps source++live).
  pose (prepared:=prepared_model_temps temps child_helper component_helper child_upper upper).
  assert (FRAME : temp_agree scope temps prepared) by (apply model_bounds_prepare_frame; assumption).
  destruct (@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal SOURCE
    scope prepared(statement_temps source)(@check_plan_frameable_writes source FRAMEABLE)
    ltac:(unfold statement_scope,scope; intros id MEMBER; apply in_or_app; left; exact MEMBER) FRAME)
    as [exit [PREPARED PUBLIC]].
  exists exit; split; [exact PREPARED|split; [exact PUBLIC|split]].
  - rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ PREPARED(statement_temps source)
      (@check_plan_frameable_writes source FRAMEABLE) child_helper
      ltac:(intro MEMBER; apply CHILD,in_or_app; left; exact MEMBER)).
    unfold prepared,prepared_model_temps; rewrite PTree.gso by congruence; apply PTree.gss.
  - rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ PREPARED(statement_temps source)
      (@check_plan_frameable_writes source FRAMEABLE) component_helper
      ltac:(intro MEMBER; apply COMPONENT,in_or_app; left; exact MEMBER)).
    unfold prepared,prepared_model_temps; apply PTree.gss.
Qed.

(** A private helper is initialized before source reasoning starts. Inserting
    an assignment of its existing value then preserves exact internal temps.
    The original source need not contain, read, or initialize that helper. *)
Lemma initialized_bound_assignment fe ge locals temps memory helper expression upper :
  temps!helper=Some(Vint upper) ->
  eval_expr ge locals temps memory expression (Vint upper) ->
  exec_stmt fe ge locals temps memory (Sset helper expression) E0 temps memory Out_normal.
Proof.
  intros WORD EVAL; rewrite <-(PTree.gsident helper temps WORD) at 2.
  constructor; exact EVAL.
Qed.

Lemma increment_preserves_private_word fe ge locals iterator helper upper temps memory trace after final outcome :
  iterator<>helper -> temps!helper=Some(Vint upper) ->
  exec_stmt fe ge locals temps memory (Ssequence Sskip(counter_increment iterator)) trace after final outcome ->
  after!helper=Some(Vint upper).
Proof.
  intros DISTINCT WORD RUN.
  rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN [iterator]
    ltac:(unfold counter_increment; repeat constructor; cbn; auto) helper
    ltac:(cbn; intuition congruence)); exact WORD.
Qed.

(** Machine-word equivalence needs no mathematical no-wrap premise. This
    bridge changes a literal header into a preinitialized private bound. It
    applies to each actually reached constant-bound body before loaded outer
    or child observations have been proved stable. *)
Theorem constant_loop_preinitialized_model fe ge locals iterator helper upper body written
  temps memory trace after final outcome :
  iterator<>helper -> writes_only written body -> ~In helper written ->
  temps!helper=Some(Vint upper) ->
  exec_stmt fe ge locals temps memory
    (strict_frontend_loop iterator(signed_expression_test iterator(Econst_int upper type_int32s)) body)
    trace after final outcome ->
  exec_stmt fe ge locals temps memory(frontend_counted_loop iterator helper body) trace after final outcome /\
  after!helper=Some(Vint upper).
Proof.
  intros DISTINCT WRITES PRIVATE WORD SOURCE.
  eapply strict_active_loop_transport with
    (invariant:=fun le _=>le!helper=Some(Vint upper))
    (body_invariant:=fun le _=>le!helper=Some(Vint upper));
    [| | | |exact SOURCE|exact WORD].
  - intros le m flag HELPER TEST.
    destruct (@signed_expression_test_facts ge locals le m iterator (Econst_int upper type_int32s) flag
      eq_refl TEST) as [counter [value [ROW [EVAL FLAG]]]].
    apply eval_const_inv in EVAL; injection EVAL as SAME; subst value; subst flag.
    apply signed_expression_test_eval; [reflexivity|exact ROW|constructor; exact HELPER].
  - intros le m tr exit last out HELPER ACTIVE RUN; split; [exact RUN|].
    rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN written WRITES helper PRIVATE); exact HELPER.
  - intros; assumption.
  - intros; eapply increment_preserves_private_word; eassumption.
Qed.

Definition constant_body_source iterator upper body :=
  Ssequence(rectangle_reset iterator)
    (strict_frontend_loop iterator(signed_expression_test iterator(Econst_int upper type_int32s)) body).
Definition constant_body_model iterator helper upper body :=
  Ssequence(Sset helper(Econst_int upper type_int32s))
    (Ssequence(rectangle_reset iterator)(frontend_counted_loop iterator helper body)).

Theorem constant_body_preinitialized_model fe ge locals iterator helper upper body written
  temps memory after final :
  iterator<>helper -> writes_only written body -> ~In helper written ->
  temps!helper=Some(Vint upper) ->
  exec_stmt fe ge locals temps memory(constant_body_source iterator upper body) E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(constant_body_model iterator helper upper body) E0 after final Out_normal /\
  after!helper=Some(Vint upper).
Proof.
  intros DISTINCT WRITES PRIVATE WORD SOURCE.
  destruct(sequence_normal_decode SOURCE) as [reset [reset_memory [RESET LOOP]]].
  destruct(rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  assert (HELPER : (PTree.set iterator(Vint Int.zero)temps)!helper=Some(Vint upper)).
  { rewrite PTree.gso by congruence; exact WORD. }
  destruct (@constant_loop_preinitialized_model fe ge locals iterator helper upper body written
    _ memory E0 after final Out_normal DISTINCT WRITES PRIVATE HELPER LOOP) as [MODEL EXIT].
  split; [|exact EXIT]; unfold constant_body_model.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=temps)(m1:=memory).
  - apply initialized_bound_assignment with(upper:=upper); [exact WORD|constructor].
  - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
Qed.

(** A captured parameter and a canonical model bound are distinct private
    resources. Equal initialized words permit a header substitution, while
    assignments in the candidate's parent body remain exact no-ops. *)
Theorem cached_loop_preinitialized_model fe ge locals iterator cache helper upper body written
  temps memory trace after final outcome :
  iterator<>cache -> iterator<>helper -> writes_only written body ->
  ~In cache written -> ~In helper written ->
  temps!cache=Some(Vint upper) -> temps!helper=Some(Vint upper) ->
  exec_stmt fe ge locals temps memory(frontend_counted_loop iterator cache body) trace after final outcome ->
  exec_stmt fe ge locals temps memory(frontend_counted_loop iterator helper body) trace after final outcome /\
  after!cache=Some(Vint upper) /\ after!helper=Some(Vint upper).
Proof.
  intros CACHE_DISTINCT HELPER_DISTINCT WRITES CACHE_PRIVATE HELPER_PRIVATE CACHE HELPER SOURCE.
  eapply strict_active_loop_transport with
    (invariant:=fun le _=>le!cache=Some(Vint upper)/\le!helper=Some(Vint upper))
    (body_invariant:=fun le _=>le!cache=Some(Vint upper)/\le!helper=Some(Vint upper));
    [| | | |exact SOURCE|split; assumption].
  - intros le m flag [CAPTURE BOUND] TEST.
    destruct (@signed_expression_test_facts ge locals le m iterator(Etempvar cache type_int32s) flag
      eq_refl TEST) as [counter [value [ROW [EVAL FLAG]]]].
    apply scalar_temp_inv in EVAL; assert (SAME : value=upper) by congruence; subst value flag.
    apply signed_expression_test_eval; [reflexivity|exact ROW|constructor; exact BOUND].
  - intros le m tr exit last out [CAPTURE BOUND] ACTIVE RUN; split; [exact RUN|split].
    + rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN written WRITES cache CACHE_PRIVATE); exact CAPTURE.
    + rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ RUN written WRITES helper HELPER_PRIVATE); exact BOUND.
  - intros; assumption.
  - intros le m tr exit last out [CAPTURE BOUND] RUN; split;
      eapply increment_preserves_private_word; eassumption.
Qed.

Definition cached_child_model column cache helper body :=
  Ssequence(Sset helper(Etempvar cache type_int32s))
    (nested_cached_body column helper body).

Theorem cached_child_preinitialized_model fe ge locals column cache helper upper body written
  temps memory after final :
  column<>cache -> column<>helper -> writes_only written body ->
  ~In cache written -> ~In helper written ->
  temps!cache=Some(Vint upper) -> temps!helper=Some(Vint upper) ->
  exec_stmt fe ge locals temps memory(nested_cached_body column cache body) E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory(cached_child_model column cache helper body) E0 after final Out_normal /\
  after!cache=Some(Vint upper) /\ after!helper=Some(Vint upper).
Proof.
  intros CACHE_DISTINCT HELPER_DISTINCT WRITES CACHE_PRIVATE HELPER_PRIVATE CACHE HELPER SOURCE.
  destruct(sequence_normal_decode SOURCE) as [reset [reset_memory [RESET LOOP]]].
  destruct(rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  assert (CAPTURE : (PTree.set column(Vint Int.zero)temps)!cache=Some(Vint upper)).
  { rewrite PTree.gso by congruence; exact CACHE. }
  assert (BOUND : (PTree.set column(Vint Int.zero)temps)!helper=Some(Vint upper)).
  { rewrite PTree.gso by congruence; exact HELPER. }
  destruct (@cached_loop_preinitialized_model fe ge locals column cache helper upper body written
    _ memory E0 after final Out_normal CACHE_DISTINCT HELPER_DISTINCT WRITES CACHE_PRIVATE HELPER_PRIVATE
    CAPTURE BOUND LOOP) as [MODEL EXIT].
  split; [|exact EXIT]; unfold cached_child_model.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=temps)(m1:=memory).
  - apply initialized_bound_assignment with(upper:=upper); [exact HELPER|constructor; exact CACHE].
  - unfold nested_cached_body; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
Qed.

Print Assumptions initialized_bound_assignment.
Print Assumptions model_bounds_prepare_execution.
Print Assumptions model_bounds_prepare_frame.
Print Assumptions model_bounds_prepare_source.
Print Assumptions increment_preserves_private_word.
Print Assumptions constant_loop_preinitialized_model.
Print Assumptions constant_body_preinitialized_model.
Print Assumptions cached_loop_preinitialized_model.
Print Assumptions cached_child_preinitialized_model.
