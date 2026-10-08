From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint
  ClightProjectedExecution ClightRegionProgress ClightStraightLine ClightRectangularLoops
  ClightCountedLoop ClightFrontendLoopProtocol ClightNoWrap ClightLoopSyntax.
From GuardInterface Require Import ClightSignedExpressionProgress ClightStrictLoopProgress
  ClightStrictIteration ClightExpressionHeaderCapture ClightNestedExpressionCapture
  ClightCheckPlanFrame ClightWordReadSnapshots ClightReadonlyLoadedTreeSynthesis ClightQuietDeterminacy
  ClightLoadedBoundSyntax.
Import ListNotations.
Set Implicit Arguments.

Definition affine_setup_child column inner_bound header body :=
  Ssequence (Sset inner_bound header)
    (Ssequence (rectangle_reset column) (frontend_counted_loop column inner_bound body)).
Definition affine_setup_source row root_bound column inner_bound header body :=
  strict_frontend_loop row (signed_expression_test row root_bound)
    (affine_setup_child column inner_bound header body).
Definition affine_setup_capture row root_cache root_bound child_cache child_pointer :=
  nested_expression_capture row root_cache root_bound child_cache (signed_load child_pointer).

Lemma affine_setup_child_quiet column inner_bound header body :
  quiet_statement body=true -> quiet_statement (affine_setup_child column inner_bound header body)=true.
Proof.
  intro QUIET; cbn [affine_setup_child quiet_statement rectangle_reset frontend_counted_loop counter_increment];
    rewrite QUIET; reflexivity.
Qed.
Lemma affine_setup_child_normal column inner_bound header body :
  quiet_statement body=true -> normal_statement (affine_setup_child column inner_bound header body)=true.
Proof.
  intro QUIET; cbn [affine_setup_child normal_statement quiet_statement rectangle_reset frontend_counted_loop counter_increment];
    rewrite QUIET; reflexivity.
Qed.

(** The child comparison licenses the assigned header word even if it is false.
    No execution or definedness of a body/RHS is asserted here. *)
Theorem affine_setup_completed_header fe ge locals temps memory column inner_bound header body after final :
  column<>inner_bound ->
  exec_stmt fe ge locals temps memory (affine_setup_child column inner_bound header body)
    E0 after final Out_normal ->
  exists word, eval_expr ge locals temps memory header (Vint word).
Proof.
  intros DISTINCT SOURCE; unfold affine_setup_child in SOURCE.
  destruct (sequence_normal_decode SOURCE) as [assigned [assigned_memory [SET TAIL]]].
  inversion SET; subst.
  destruct (sequence_normal_decode TAIL) as [reset [reset_memory [RESET CHILD]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  change (frontend_counted_loop column inner_bound body) with
    (strict_frontend_loop column (signed_expression_test column (Etempvar inner_bound type_int32s)) body) in CHILD.
  destruct (signed_expression_completed_header CHILD) as [flag TEST].
  destruct (@signed_expression_test_facts _ _ _ _ column (Etempvar inner_bound type_int32s) _ eq_refl TEST)
    as [counter [word [ROW [BOUND FLAG]]]].
  apply scalar_temp_inv in BOUND.
  rewrite PTree.gso in BOUND by congruence; rewrite PTree.gss in BOUND.
  injection BOUND as VALUE; subst.
  exists word; assumption.
Qed.

Lemma snapshot_word_read_in_temps code : snapshot_word_expression code ->
  forall pointer, In pointer (snapshot_word_reads code) -> In pointer (expression_temps code).
Proof.
  intro WORD; induction WORD; intros observed_pointer MEMBER;
    cbn [snapshot_word_reads expression_temps signed_load signed_pointer_temp] in *; try contradiction.
  - exact MEMBER.
  - apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app;
      [left; apply IHWORD1|right; apply IHWORD2]; exact MEMBER.
Qed.
Lemma affine_setup_header_scope row root_bound column inner_bound header body :
  incl (expression_temps header)
    (statement_temps (affine_setup_source row root_bound column inner_bound header body)).
Proof.
  unfold affine_setup_source,affine_setup_child,strict_frontend_loop;
    cbn [statement_temps]; intros identifier MEMBER;
    repeat rewrite in_app_iff; cbn; tauto.
Qed.

(** Capture the raw read in a reached affine setup, rather than the first
    entire bound (which changes with the row coordinate). The source remains
    unchanged after capture. Future stability is a separate domain obligation. *)
Theorem affine_setup_capture_execution fe ge locals temps memory row root_bound column inner_bound header body
    root_cache child_cache child_pointer live after final :
  typeof root_bound=type_int32s -> snapshot_word_expression header ->
  In child_pointer (snapshot_word_reads header) -> column<>inner_bound -> quiet_statement body=true ->
  check_plan_frameable (affine_setup_source row root_bound column inner_bound header body)=true ->
  ~In root_cache (statement_temps (affine_setup_source row root_bound column inner_bound header body)++live) ->
  ~In child_cache (statement_temps (affine_setup_source row root_bound column inner_bound header body)++live) ->
  root_cache<>child_cache ->
  exec_stmt fe ge locals temps memory (affine_setup_source row root_bound column inner_bound header body)
    E0 after final Out_normal ->
  exists upper child prepared_after,
    exec_stmt fe ge locals temps memory (affine_setup_capture row root_cache root_bound child_cache child_pointer)
      E0 (nested_expression_captured root_cache child_cache temps upper child) memory Out_normal /\
    exec_stmt fe ge locals (nested_expression_captured root_cache child_cache temps upper child) memory
      (affine_setup_source row root_bound column inner_bound header body)
      E0 prepared_after final Out_normal /\
    temp_agree (statement_temps (affine_setup_source row root_bound column inner_bound header body)++live)
      after prepared_after /\
    eval_expr ge locals temps memory root_bound (Vint upper) /\
    (match child with
     | None => Int.lt (temp_word row temps) upper=false
     | Some word => Int.lt (temp_word row temps) upper=true /\
         eval_expr ge locals temps memory (signed_load child_pointer) (Vint word)
     end).
Proof.
  intros ROOT_TYPE WORD MEMBER DISTINCT QUIET FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE CACHES SOURCE.
  pose (source := affine_setup_source row root_bound column inner_bound header body).
  pose (scope := statement_temps source++live).
  destruct (@signed_expression_capture_receipt fe ge locals temps memory row root_bound
    (affine_setup_child column inner_bound header body) root_cache live after final ROOT_TYPE
    (@affine_setup_child_normal column inner_bound header body QUIET)
    (@affine_setup_child_quiet column inner_bound header body QUIET) FRAMEABLE ROOT_PRIVATE SOURCE)
    as [upper [root_after [ROOT_CAPTURE [PREPARED [PUBLIC [RECEIPT ROOT_EVAL]]]]]].
  assert (ROOT_FRAME : temp_agree scope temps (PTree.set root_cache (Vint upper) temps)).
  { apply temp_agree_set; exact ROOT_PRIVATE. }
  assert (ROW_MEMBER : In row scope).
  { unfold scope,source,affine_setup_source,strict_frontend_loop,signed_expression_test;
      cbn [statement_temps expression_temps]; repeat rewrite in_app_iff; cbn; tauto. }
  destruct (signed_expression_completed_header SOURCE) as [flag TEST].
  destruct (@signed_expression_test_facts _ _ _ _ _ _ _ ROOT_TYPE TEST)
    as [counter [observed [ROW [EVAL FLAG]]]].
  pose proof (proj1 (expressions_determinate ge locals temps memory) _ _ EVAL _ ROOT_EVAL) as SAME.
  injection SAME as VALUE; subst observed.
  assert (COUNTER : temp_word row temps=counter) by (unfold temp_word; rewrite ROW; reflexivity).
  assert (CAPTURE_TEST : expression_test (signed_expression_test row (Etempvar root_cache type_int32s))
    (Entry ge locals (PTree.set root_cache (Vint upper) temps) memory) (Int.lt counter upper)).
  { apply signed_expression_test_eval; [reflexivity|rewrite ROOT_FRAME by exact ROW_MEMBER; exact ROW|
      apply eval_Etempvar,PTree.gss]. }
  destruct (Int.lt counter upper) eqn:ACTIVE.
  - assert (ACTUAL_ACTIVE : expression_test (signed_expression_test row root_bound)
      (Entry ge locals temps memory) true).
    { rewrite <-ACTIVE; apply signed_expression_test_eval;
        [exact ROOT_TYPE|exact ROW|exact ROOT_EVAL]. }
    destruct (@strict_active_iteration fe ge locals row (signed_expression_test row root_bound)
      (affine_setup_child column inner_bound header body) temps memory after final
      (@affine_setup_child_normal column inner_bound header body QUIET)
      (@affine_setup_child_quiet column inner_bound header body QUIET) ACTUAL_ACTIVE SOURCE)
      as [body_after [body_final [next [next_memory [BODY REST]]]]].
    destruct (@affine_setup_completed_header fe ge locals temps memory column inner_bound header body
      body_after body_final DISTINCT BODY) as [bound HEADER].
    destruct (@snapshot_word_reads_defined header WORD ge locals temps memory bound HEADER child_pointer MEMBER)
      as [word READ].
    assert (CAPTURE_READ : eval_expr ge locals (PTree.set root_cache (Vint upper) temps) memory
      (signed_load child_pointer) (Vint word)).
    { eapply expression_temp_transport; [|exact ROOT_FRAME|exact READ].
      intros identifier IN; cbn [signed_load signed_pointer_temp expression_temps] in IN.
      destruct IN as [<-|[]]; unfold scope,source; apply in_or_app; left;
        apply affine_setup_header_scope; eapply snapshot_word_read_in_temps; eassumption. }
    destruct (@structured_execution_temp_transport fe ge locals (PTree.set root_cache (Vint upper) temps) memory
      source E0 root_after final Out_normal PREPARED scope
      (PTree.set child_cache (Vint word) (PTree.set root_cache (Vint upper) temps))
      (statement_temps source) (@check_plan_frameable_writes source FRAMEABLE)
      ltac:(unfold statement_scope,scope; intros identifier IN; apply in_or_app; left; exact IN)
      (@temp_agree_set scope _ child_cache (Vint word) CHILD_PRIVATE))
      as [prepared_after [PREPARED_CHILD CHILD_PUBLIC]].
    exists upper,(Some word),prepared_after.
    split; [|split; [exact PREPARED_CHILD|split; [eapply temp_agree_trans; eassumption|split; [exact ROOT_EVAL|]]]].
    + unfold affine_setup_capture,nested_expression_capture,nested_expression_captured.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact ROOT_CAPTURE|].
      destruct CAPTURE_TEST as [value [EVAL_CAPTURE BOOL]];
        eapply exec_Sifthenelse; [exact EVAL_CAPTURE|exact BOOL|constructor; exact CAPTURE_READ].
    + split; [rewrite COUNTER; exact ACTIVE|exact READ].
  - exists upper,None,root_after.
    split; [|split; [exact PREPARED|split; [exact PUBLIC|split; [exact ROOT_EVAL|rewrite COUNTER; exact ACTIVE]]]].
    unfold affine_setup_capture,nested_expression_capture,nested_expression_captured.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact ROOT_CAPTURE|].
    destruct CAPTURE_TEST as [value [EVAL_CAPTURE BOOL]];
      eapply exec_Sifthenelse; [exact EVAL_CAPTURE|exact BOOL|constructor].
Qed.

Print Assumptions affine_setup_completed_header.
Print Assumptions affine_setup_capture_execution.
