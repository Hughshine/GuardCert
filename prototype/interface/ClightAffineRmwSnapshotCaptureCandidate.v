From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightTempFrame ClightTempFootprint ClightStraightLine
  ClightPrivateRegion ClightLoopSyntax CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth GuardMemoryPointerSequence.
From GuardInterface Require Import ClightAffineSnapshotSyntax ClightAffineSnapshotRows ClightAffineHeaderSnapshots
  ClightAffineSnapshotSourceInputs ClightAffineRmwSnapshotCondition ClightAffineRmwSnapshotCandidateExecution
  ClightAffineZeroPointerCandidate ClightAffineInnerPointerSourceGuard ClightAffinePointerGuard
  ClightSourceObservation ClightNestedExpressionCapture ClightCheckPlanFrame ClightLoadedBoundSyntax ClightAffineSnapshotCaptureCandidate ClightFirstReachedWidth ClightAffineZeroSnapshotPreparation ClightAffineSnapshotRowObservation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section CAPTURE.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Variable rmw : affine_snapshot_rmw_site site.
Variable live : list ident.
Variable capture : affine_snapshot_capture_package site live.
Let package := snapshot_cached_package site.
Variable candidate : affine_zero_pointer_candidate_package package live.
Variables first later alias : decision_tree.
Hypothesis FIRST : compile_first_reached_width 0(affine_inner_pointer_column_limit package)0
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some first.
Hypothesis LATER : compile_first_reached_width 0(affine_inner_pointer_column_limit package)1
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some later.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package=Some alias.
Definition affine_rmw_snapshot_captured_guarded_candidate :=
  Ssequence(affine_snapshot_capture_statement site)(affine_rmw_snapshot_guarded_candidate rmw candidate first later alias).

Theorem affine_rmw_snapshot_captured_candidate_execution fe ge locals temps memory after final :
  observed_pointer_domain(affine_inner_pointer_pointers package)(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exists target,exec_stmt fe ge locals temps memory affine_rmw_snapshot_captured_guarded_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros OBSERVED SOURCE.
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
    as [upper [child [checked [source_after [CAPTURE [CHECKED [PREPARED [PUBLIC DOMAIN]]]]]]]].
  assert(POINTERS:observed_pointer_domain(affine_inner_pointer_pointers package)(Entry ge locals checked memory)).
  { eapply(@observed_pointer_domain_frame(affine_inner_pointer_pointers package)
      (Entry ge locals temps memory)(Entry ge locals checked memory)); [reflexivity| |exact OBSERVED].
    rewrite CHECKED; eapply temp_agree_weaken; [|apply nested_expression_captured_frame; [exact ROOT_PRIVATE|exact CHILD_PRIVATE]].
    intros identifier MEMBER; apply in_or_app; right; apply in_or_app; right; exact MEMBER. }
  rewrite <-snapshot_source_exact in PREPARED.
  destruct(@affine_rmw_snapshot_guarded_candidate_execution original site rmw live candidate first later alias FIRST LATER ALIAS
    fe ge locals checked memory source_after final(conj DOMAIN POINTERS)PREPARED)
    as [target [EXECUTE FRAME]].
  exists target; split.
  - unfold affine_rmw_snapshot_captured_guarded_candidate; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
  - eapply temp_agree_trans; [|exact FRAME].
    eapply temp_agree_weaken; [|exact PUBLIC]; intros identifier MEMBER;
      apply in_or_app; right; apply in_or_app; left; exact MEMBER.
Qed.

(** Actual retained source loads license pointer comparisons. The injected
    captures are licensed by the reached original headers, including the empty
    outer case, where the child load is skipped. The contract fits the existing
    finite-region host; installing it still needs checked progress and scope. *)
Theorem affine_rmw_snapshot_observed_captured_candidate_contract loads :
  source_observations_check(affine_inner_pointer_pointers package)loads=true ->
  PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)
    (Ssequence(source_load_prefix loads)affine_rmw_snapshot_captured_guarded_candidate).
Proof.
  intro CHECK; destruct(@source_observations_check_sound(affine_inner_pointer_pointers package)loads CHECK)as [COVER FRESH].
  apply source_prefix_region_contract with
    (writes:=source_load_targets loads++statement_temps original)
    (domain:=observed_pointer_domain(affine_inner_pointer_pointers package)).
  - apply source_load_prefix_supported.
  - apply writes_sequence.
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; left; exact MEMBER|apply source_load_prefix_writes].
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; right; exact MEMBER|].
      apply check_plan_frameable_writes; exact(snapshot_capture_frameable capture).
  - intros temps p locals entry memory middle after final PREFIX BODY.
    destruct(@source_load_prefix_observations loads(adapter_entry temps)(globalenv p)locals entry memory
      E0 middle memory Out_normal FRESH PREFIX)as [_ [_ [_ OBSERVED]]].
    intros identifier MEMBER; apply OBSERVED,COVER; exact MEMBER.
  - intros temps p locals entry memory after final SCOPE OBSERVED SOURCE.
    destruct(@affine_rmw_snapshot_captured_candidate_execution(adapter_entry temps)(globalenv p)locals entry memory
      after final OBSERVED SOURCE)as [target [EXECUTE PUBLIC]].
    exists target,final; split; [exact EXECUTE|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.
End CAPTURE.

Print Assumptions affine_rmw_snapshot_captured_candidate_execution.
Print Assumptions affine_rmw_snapshot_observed_captured_candidate_contract.
