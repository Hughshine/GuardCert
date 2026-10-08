From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightGuard ClightPrivateRegion
  ClightRegionProgress ClightTempFootprint ClightStraightLine ClightLoopSyntax CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryPointerSequence.
From GuardInterface Require Import ClightAffineSnapshotSyntax ClightAffineSnapshotRows
  ClightAffineSnapshotSourceInputs ClightAffineSnapshotCaptureCandidate ClightAffineHeaderSnapshots
  ClightNestedExpressionCapture ClightLoadedBoundSyntax ClightAffineEmptyWidth
  ClightAffineZeroSnapshotPreparation ClightAffineEmptySnapshotRewrite ClightSourceObservation
  ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.

Section CAPTURE.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Variable live : list ident.
Variable capture : affine_snapshot_capture_package site live.
Let package:=snapshot_cached_package site.
Variable width : decision_tree.
Hypothesis WIDTH : compile_affine_empty_width
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some width.

Definition affine_empty_snapshot_captured:=Ssequence(affine_snapshot_capture_statement site)
  (affine_empty_snapshot_guarded site width).

Theorem affine_empty_snapshot_captured_execution fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exists target,exec_stmt fe ge locals temps memory affine_empty_snapshot_captured E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intro SOURCE.
  assert(FRAMEABLE:check_plan_frameable(affine_snapshot_source package(snapshot_root site)
    (snapshot_original_header site))=true).
  { rewrite <-snapshot_source_exact; exact(snapshot_capture_frameable capture). }
  assert(ROOT_PRIVATE:~In(affine_inner_pointer_bound(affine_inner_pointer_shape package))
    (statement_temps(affine_snapshot_source package(snapshot_root site)(snapshot_original_header site))++
      (live++affine_inner_pointer_pointers package))).
  { rewrite <-snapshot_source_exact; exact(snapshot_capture_root_private capture). }
  assert(CHILD_PRIVATE:~In(snapshot_child_cache site)
    (statement_temps(affine_snapshot_source package(snapshot_root site)(snapshot_original_header site))++
      (live++affine_inner_pointer_pointers package))).
  { rewrite <-snapshot_source_exact; exact(snapshot_capture_child_private capture). }
  rewrite(snapshot_source_exact site)in SOURCE.
  destruct(@affine_snapshot_capture_source_inputs(snapshot_cached_source site)package(snapshot_root site)
    (snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
    (live++affine_inner_pointer_pointers package)fe ge locals temps memory after final
    (snapshot_header_word site)(snapshot_child_read site)
    (@memory_pointer_sequence_quiet _ _(affine_inner_pointer_body_exact(affine_inner_pointer_syntax package)))
    FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE(snapshot_capture_caches_distinct capture)SOURCE)
    as [upper[child[checked[source_after[CAPTURE[CHECKED[PREPARED[PUBLIC DOMAIN]]]]]]]].
  rewrite <-snapshot_source_exact in PREPARED.
  exists source_after; split.
  - unfold affine_empty_snapshot_captured; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0);
      [exact CAPTURE|].
    exact(@affine_empty_snapshot_guarded_execution original site width WIDTH fe ge locals checked memory
      source_after final DOMAIN PREPARED).
  - eapply temp_agree_weaken; [|exact PUBLIC].
    intros id MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
Qed.

Theorem affine_empty_snapshot_prefix_contract loads :
  PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)
    (Ssequence(source_load_prefix loads)affine_empty_snapshot_captured).
Proof.
  apply source_prefix_region_contract with
    (writes:=source_load_targets loads++statement_temps original)(domain:=fun _=>True).
  - apply source_load_prefix_supported.
  - apply writes_sequence.
    + eapply writes_only_weaken; [intros id MEMBER; apply in_or_app; left; exact MEMBER|apply source_load_prefix_writes].
    + eapply writes_only_weaken; [intros id MEMBER; apply in_or_app; right; exact MEMBER|].
      apply check_plan_frameable_writes; exact(snapshot_capture_frameable capture).
  - intros; exact I.
  - intros temps p locals entry memory after final SCOPE DOMAIN SOURCE.
    destruct(@affine_empty_snapshot_captured_execution(adapter_entry temps)(globalenv p)locals entry memory
      after final SOURCE)as [target[EXECUTE PUBLIC]].
    exists target,final; split; [exact EXECUTE|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.
End CAPTURE.

Print Assumptions affine_empty_snapshot_captured_execution.
Print Assumptions affine_empty_snapshot_prefix_contract.
