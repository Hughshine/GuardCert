From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightLoopSyntax ClightRegionProgress CompCertMemoryActions.
From GuardInterface Require Import ClightNestedExpressionCapture ClightNestedExpressionTransport
  ClightStrictLoopProgress ClightSignedExpressionProgress ClightLoadedOffsetHeader ClightLoadedBoundSyntax ClightObservedHeaderPrefix ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition nested_loaded_offset_source row pointer delta column child_pointer child_delta body :=
  nested_expression_source row (signed_load_offset pointer delta) column
    (signed_load_offset child_pointer child_delta) body.
Definition nested_loaded_offset_observations pointer child_pointer entry :=
  loaded_offset_observations pointer entry++loaded_offset_observations child_pointer entry.

Lemma nested_loaded_offset_observations_initial pointer delta cache child_pointer child_delta child_cache entry :
  loaded_offset_cached_header pointer delta cache entry ->
  loaded_offset_cached_header child_pointer child_delta child_cache entry ->
  header_observations_match (nested_loaded_offset_observations pointer child_pointer entry) (entry_memory entry).
Proof.
  intros ROOT CHILD; unfold header_observations_match,nested_loaded_offset_observations; apply Forall_app; split;
    eapply loaded_offset_initial_observations; eassumption.
Qed.

Lemma nested_loaded_offset_outer_header pointer child_pointer delta cache stable entry current memory upper :
  In pointer stable -> loaded_offset_cached_header pointer delta cache entry ->
  (entry_temps entry)!cache=Some(Vint upper) -> temp_agree stable (entry_temps entry) current ->
  header_observations_match (nested_loaded_offset_observations pointer child_pointer entry) memory ->
  eval_expr (entry_ge entry) (entry_env entry) current memory (signed_load_offset pointer delta) (Vint upper).
Proof.
  intros MEMBER SNAPSHOT CACHE FRAME OBSERVED.
  unfold header_observations_match,nested_loaded_offset_observations in OBSERVED; apply Forall_app in OBSERVED as [ROOT CHILD].
  eapply loaded_offset_bound_from_observations; eassumption.
Qed.
Lemma nested_loaded_offset_child_header pointer child_pointer delta child_cache stable entry current memory upper :
  In child_pointer stable -> loaded_offset_cached_header child_pointer delta child_cache entry ->
  (entry_temps entry)!child_cache=Some(Vint upper) -> temp_agree stable (entry_temps entry) current ->
  header_observations_match (nested_loaded_offset_observations pointer child_pointer entry) memory ->
  eval_expr (entry_ge entry) (entry_env entry) current memory (signed_load_offset child_pointer delta) (Vint upper).
Proof.
  intros MEMBER SNAPSHOT CACHE FRAME OBSERVED.
  unfold header_observations_match,nested_loaded_offset_observations in OBSERVED; apply Forall_app in OBSERVED as [ROOT CHILD].
  eapply loaded_offset_bound_from_observations; eassumption.
Qed.

(** Completion of the original nested source licenses both captures. The
    child snapshot exists only when the original outer comparison was true. *)
Theorem nested_loaded_offset_capture fe ge locals temps memory row pointer delta column child_pointer child_delta body
  cache child_cache live after final :
  quiet_statement body=true ->
  check_plan_frameable (nested_loaded_offset_source row pointer delta column child_pointer child_delta body)=true ->
  ~In cache (statement_temps (nested_loaded_offset_source row pointer delta column child_pointer child_delta body)++live) ->
  ~In child_cache (statement_temps (nested_loaded_offset_source row pointer delta column child_pointer child_delta body)++live) ->
  cache<>child_cache -> column<>child_pointer ->
  exec_stmt fe ge locals temps memory (nested_loaded_offset_source row pointer delta column child_pointer child_delta body)
    E0 after final Out_normal ->
  exists upper child prepared_after,
    exec_stmt fe ge locals temps memory
      (nested_expression_capture row cache (signed_load_offset pointer delta) child_cache (signed_load_offset child_pointer child_delta))
      E0 (nested_expression_captured cache child_cache temps upper child) memory Out_normal /\
    exec_stmt fe ge locals (nested_expression_captured cache child_cache temps upper child) memory
      (nested_loaded_offset_source row pointer delta column child_pointer child_delta body) E0 prepared_after final Out_normal /\
    temp_agree (statement_temps (nested_loaded_offset_source row pointer delta column child_pointer child_delta body)++live)
      after prepared_after /\
    loaded_offset_cached_header pointer delta cache
      (Entry ge locals (nested_expression_captured cache child_cache temps upper child) memory) /\
    (match child with
    | None => Int.lt (temp_word row temps) upper=false
    | Some word => Int.lt (temp_word row temps) upper=true /\
        loaded_offset_cached_header child_pointer child_delta child_cache
          (Entry ge locals (nested_expression_captured cache child_cache temps upper child) memory)
    end).
Proof.
  intros QUIET FRAMEABLE PRIVATE CHILD_PRIVATE DISTINCT CHILD_DISTINCT SOURCE.
  destruct (@nested_expression_capture_execution fe ge locals temps memory row (signed_load_offset pointer delta)
    column (signed_load_offset child_pointer child_delta) body cache child_cache live after final eq_refl eq_refl
    QUIET FRAMEABLE PRIVATE CHILD_PRIVATE DISTINCT ltac:(cbn; intuition congruence) SOURCE)
    as [upper [child [prepared_after [CAPTURE [PREPARED [PUBLIC [EVAL CHILD]]]]]]].
  pose (source := nested_loaded_offset_source row pointer delta column child_pointer child_delta body).
  pose (scope := statement_temps source++live).
  assert (FRAME : temp_agree scope temps (nested_expression_captured cache child_cache temps upper child)).
  { apply nested_expression_captured_frame; assumption. }
  assert (ROOT_MEMBER : In pointer scope).
  { unfold scope,source,nested_loaded_offset_source,nested_expression_source,strict_frontend_loop;
    cbn [statement_temps expression_temps signed_expression_test signed_load_offset signed_load signed_pointer_temp];
    repeat rewrite in_app_iff; cbn; tauto. }
  assert (CHILD_MEMBER : In child_pointer scope).
  { unfold scope,source,nested_loaded_offset_source,nested_expression_source,nested_expression_body,strict_frontend_loop;
    cbn [statement_temps expression_temps signed_expression_test signed_load_offset signed_load signed_pointer_temp];
    repeat rewrite in_app_iff; cbn; tauto. }
  exists upper,child,prepared_after.
  split; [exact CAPTURE|split; [exact PREPARED|split; [exact PUBLIC|split]]].
  - destruct (signed_load_offset_inv EVAL) as [block [offset [raw [POINTER [READ WORD]]]]].
    exists block,offset,raw; cbn [entry_temps entry_memory].
    split; [rewrite FRAME by exact ROOT_MEMBER; exact POINTER|split; [exact READ|]].
    rewrite nested_expression_captured_root by exact DISTINCT; rewrite WORD; reflexivity.
  - destruct child as [child_word|]; [destruct CHILD as [ACTIVE CHILD_EVAL]; split; [exact ACTIVE|]|exact CHILD].
    destruct (signed_load_offset_inv CHILD_EVAL) as [block [offset [raw [POINTER [READ WORD]]]]].
    exists block,offset,raw; cbn [entry_temps entry_memory].
    split; [rewrite FRAME by exact CHILD_MEMBER; exact POINTER|split; [exact READ|]].
    rewrite nested_expression_captured_child,WORD; reflexivity.
Qed.

(** The optimizer's point checks preserve the whole observation list. The
    language services derive execution of both cached loops from the actual
    original nest; it is not an input supplied by the optimizer. *)
Theorem nested_loaded_offset_initial_cached fe ge locals temps memory row pointer delta column child_pointer child_delta
  cache child_cache body stable written after final :
  In pointer stable -> In child_pointer stable -> In cache stable -> In child_cache stable ->
  ~In row stable -> ~In column stable -> row<>column ->
  normal_statement body=true -> quiet_statement body=true -> writes_only written body ->
  ~In row written -> ~In column written -> (forall id,In id stable -> ~In id written) ->
  loaded_offset_cached_header pointer delta cache (Entry ge locals temps memory) ->
  loaded_offset_cached_header child_pointer child_delta child_cache (Entry ge locals temps memory) ->
  0<=Int.signed(temp_word cache temps) -> 0<=Int.signed(temp_word child_cache temps) ->
  temps!row=Some(Vint Int.zero) ->
  (forall i j current before exit last,
    0<=i<Int.signed(temp_word cache temps) -> 0<=j<Int.signed(temp_word child_cache temps) ->
    current!row=Some(Vint(Int.repr i)) -> current!column=Some(Vint(Int.repr j)) ->
    temp_agree stable temps current ->
    header_observations_match (nested_loaded_offset_observations pointer child_pointer (Entry ge locals temps memory)) before ->
    exec_stmt fe ge locals current before body E0 exit last Out_normal ->
    header_observations_match (nested_loaded_offset_observations pointer child_pointer (Entry ge locals temps memory)) last) ->
  exec_stmt fe ge locals temps memory (nested_loaded_offset_source row pointer delta column child_pointer child_delta body)
    E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory (nested_cached_source row cache column child_cache body) E0 after final Out_normal /\
  header_observations_match (nested_loaded_offset_observations pointer child_pointer (Entry ge locals temps memory)) final.
Proof.
  intros POINTER_MEMBER CHILD_POINTER_MEMBER CACHE_MEMBER CHILD_CACHE_MEMBER ROW_FRESH COLUMN_FRESH DISTINCT
    NORMAL QUIET WRITES ROW_UNWRITTEN COLUMN_UNWRITTEN STABLE_UNWRITTEN ROOT CHILD NONNEGATIVE CHILD_NONNEGATIVE
    ROW PRESERVE SOURCE.
  assert (CACHE : temps!cache=Some(Vint(temp_word cache temps))).
  { destruct ROOT as [block [offset [raw [POINTER [READ WORD]]]]]; cbn [entry_temps] in WORD;
    unfold temp_word; rewrite WORD; reflexivity. }
  assert (CHILD_CACHE : temps!child_cache=Some(Vint(temp_word child_cache temps))).
  { destruct CHILD as [block [offset [raw [POINTER [READ WORD]]]]]; cbn [entry_temps] in WORD;
    unfold temp_word; rewrite WORD; reflexivity. }
  eapply nested_expression_initial_cached with (stable:=stable) (written:=written)
    (upper:=temp_word cache temps) (child_upper:=temp_word child_cache temps);
    try eassumption; try reflexivity.
  - intros i current before RANGE CURRENT FRAME OBSERVED.
    eapply nested_loaded_offset_outer_header with (entry:=Entry ge locals temps memory) (cache:=cache);
      eassumption.
  - intros i j current before IR JR CURRENT COLUMN FRAME OBSERVED.
    eapply nested_loaded_offset_child_header with (entry:=Entry ge locals temps memory) (child_cache:=child_cache);
      eassumption.
  - eapply nested_loaded_offset_observations_initial; eassumption.
Qed.

Print Assumptions nested_loaded_offset_observations_initial.
Print Assumptions nested_loaded_offset_outer_header.
Print Assumptions nested_loaded_offset_child_header.
Print Assumptions nested_loaded_offset_capture.
Print Assumptions nested_loaded_offset_initial_cached.
