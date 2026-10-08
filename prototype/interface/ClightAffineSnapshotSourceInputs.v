From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint
  ClightNoWrap ClightLoopSyntax ClightRegionProgress ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightWordReadSnapshots
  ClightAffineHeaderSnapshots ClightAffineSnapshotRows ClightNestedExpressionCapture ClightCheckPlanFrame
  ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.

(** The body remains the original loaded source. Neither future stability nor
    completion of a cached loop is an invocation assumption. *)
Definition affine_snapshot_original_domain source(package:memory_affine_inner_pointer_package source)
  root child child_cache header fe entry :=
  cached_signed_read root(affine_inner_pointer_bound(affine_inner_pointer_shape package))entry /\
  (Int.lt(temp_word(affine_inner_pointer_row(affine_inner_pointer_shape package))(entry_temps entry))
    (temp_word(affine_inner_pointer_bound(affine_inner_pointer_shape package))(entry_temps entry))=true ->
    cached_signed_read child child_cache entry) /\
  exists after final, exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (affine_snapshot_source package root header)E0 after final Out_normal.

Theorem affine_snapshot_capture_source_inputs source(package:memory_affine_inner_pointer_package source)
    root child child_cache header live fe ge locals temps memory after final :
  snapshot_word_expression header -> In child(snapshot_word_reads header) ->
  quiet_statement(affine_inner_pointer_body(affine_inner_pointer_shape package))=true ->
  check_plan_frameable(affine_snapshot_source package root header)=true ->
  ~In(affine_inner_pointer_bound(affine_inner_pointer_shape package))
    (statement_temps(affine_snapshot_source package root header)++live) ->
  ~In child_cache(statement_temps(affine_snapshot_source package root header)++live) ->
  affine_inner_pointer_bound(affine_inner_pointer_shape package)<>child_cache ->
  exec_stmt fe ge locals temps memory(affine_snapshot_source package root header)E0 after final Out_normal ->
  exists upper captured checked source_after,
    exec_stmt fe ge locals temps memory
      (affine_setup_capture(affine_inner_pointer_row(affine_inner_pointer_shape package))
        (affine_inner_pointer_bound(affine_inner_pointer_shape package))(signed_load root)child_cache child)
      E0 checked memory Out_normal /\
    checked=nested_expression_captured(affine_inner_pointer_bound(affine_inner_pointer_shape package))
      child_cache temps upper captured /\
    exec_stmt fe ge locals checked memory(affine_snapshot_source package root header)E0 source_after final Out_normal /\
    temp_agree(statement_temps(affine_snapshot_source package root header)++live)after source_after /\
    affine_snapshot_original_domain package root child child_cache header fe(Entry ge locals checked memory).
Proof.
  intros WORD MEMBER QUIET FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE CACHES SOURCE.
  pose(shape:=affine_inner_pointer_shape package).
  pose(row:=affine_inner_pointer_row shape).
  pose(column:=affine_inner_pointer_column shape).
  pose(inner_bound:=affine_inner_pointer_inner_bound shape).
  pose(cache:=affine_inner_pointer_bound shape).
  pose(scope:=statement_temps(affine_snapshot_source package root header)++live).
  pose proof(affine_inner_pointer_ck(affine_inner_pointer_syntax package))as CK.
  change(column<>inner_bound)in CK.
  destruct(@affine_setup_capture_execution fe ge locals temps memory row(signed_load root)
    column inner_bound header(affine_inner_pointer_body shape)cache child_cache child live after final
    eq_refl WORD MEMBER CK QUIET FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE CACHES SOURCE)
    as [upper [captured [source_after [CAPTURE [PREPARED [PUBLIC [ROOT_EVAL CHILD_EVAL]]]]]]].
  pose(checked:=nested_expression_captured cache child_cache temps upper captured).
  assert(FRAME:temp_agree scope temps checked).
  { apply nested_expression_captured_frame; assumption. }
  assert(ROOT_MEMBER:In root scope).
  { unfold scope,affine_snapshot_source,loaded_bound_test,strict_frontend_loop,signed_load,signed_pointer_temp;
      cbn [statement_temps expression_temps]; repeat rewrite in_app_iff; cbn; tauto. }
  assert(ROW_MEMBER:In row scope).
  { unfold scope,affine_snapshot_source,loaded_bound_test,strict_frontend_loop,row,shape;
      cbn [statement_temps expression_temps]; repeat rewrite in_app_iff; cbn; tauto. }
  assert(CHILD_MEMBER:In child scope).
  { unfold scope; apply in_or_app; left; change(In child
      (statement_temps(affine_setup_source row(signed_load root)column inner_bound header(affine_inner_pointer_body shape)))).
    apply affine_setup_header_scope; eapply snapshot_word_read_in_temps; eassumption. }
  assert(CACHE:checked!cache=Some(Vint upper)).
  { unfold checked; apply nested_expression_captured_root; exact CACHES. }
  assert(ROOT:cached_signed_read root cache(Entry ge locals checked memory)).
  { destruct(signed_load_inv ROOT_EVAL)as [block [offset [POINTER READ]]].
    exists block,offset,upper; cbn [entry_temps entry_memory]; split;
      [rewrite FRAME by exact ROOT_MEMBER; exact POINTER|split; assumption]. }
  exists upper,captured,checked,source_after.
  split; [exact CAPTURE|split; [reflexivity|split; [exact PREPARED|split; [exact PUBLIC|]]]].
  unfold affine_snapshot_original_domain; split; [exact ROOT|split; [|exists source_after,final; exact PREPARED]].
  intro ACTIVE; destruct captured as [word|].
  - destruct CHILD_EVAL as [_ READ].
    destruct(signed_load_inv READ)as [block [offset [POINTER LOADED]]].
    exists block,offset,word; cbn [entry_temps entry_memory]; split.
    + rewrite FRAME by exact CHILD_MEMBER; exact POINTER.
    + split; [unfold checked; apply nested_expression_captured_child|exact LOADED].
  - cbn [entry_temps]in ACTIVE; change(Int.lt(temp_word row checked)(temp_word cache checked)=true)in ACTIVE.
    unfold temp_word in ACTIVE; rewrite CACHE,(FRAME row ROW_MEMBER)in ACTIVE.
    change(Int.lt(temp_word row temps)upper=true)in ACTIVE; congruence.
Qed.

Print Assumptions affine_snapshot_capture_source_inputs.
