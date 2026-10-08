From Stdlib Require Import List ZArith.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightGuard ClightPrivateRegion
  ClightLoopSyntax CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth.
From GuardInterface Require Import ClightAffineSnapshotSyntax ClightAffineZeroSnapshotCaptureCandidate
  ClightAffineZeroSnapshotCandidateExecution ClightAffineZeroSnapshotCheckPlan ClightAffineZeroPointerCandidate
  ClightAffineInnerPointerSourceGuard ClightAffinePointerGuard ClightSourceObservation ClightReadonlyRewrite
  ClightCheckPlan ClightCheckPlanFrame ClightAffineSnapshotCaptureCandidate ClightFirstReachedWidth ClightAffineZeroSnapshotPreparation.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section REWRITE.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Variable live : list ident.
Variable capture : affine_snapshot_capture_package site live.
Let package:=snapshot_cached_package site.
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
Let plan:=affine_zero_snapshot_complete_check_plan site first later alias
  (affine_zero_candidate_validator_bounds candidate)(affine_zero_candidate_encoder_bounds candidate).
Let yes:=affine_zero_pointer_candidate_statement candidate.
Variable result : ident.
Hypotheses (YES:check_plan_frameable yes=true)(NO:check_plan_frameable original=true).
Hypothesis PRIVATE : ~In result(check_plan_reads plan++statement_temps yes++statement_temps original++live).

Definition affine_zero_snapshot_planned_captured_candidate :=
  Ssequence(affine_snapshot_capture_statement site)(check_plan_guarded_statement plan result yes original).

(** Reuse the actual original/cached/model/candidate execution proof. The
    private Boolean transports the selected branch and public exit; no new
    assumption encoding or candidate certificate is required. *)
Theorem affine_zero_snapshot_planned_captured_candidate_execution fe ge locals temps memory after final :
  observed_pointer_domain(affine_inner_pointer_pointers package)(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exists target,exec_stmt fe ge locals temps memory affine_zero_snapshot_planned_captured_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros OBSERVED SOURCE.
  destruct(@affine_zero_snapshot_captured_candidate_execution original site live capture candidate first later alias FIRST LATER ALIAS
    fe ge locals temps memory after final OBSERVED SOURCE)as [old [RUN PUBLIC]].
  unfold affine_zero_snapshot_captured_guarded_candidate in RUN.
  destruct(sequence_normal_decode RUN)as [checked [checked_memory [CAPTURE SELECT]]].
  unfold affine_zero_snapshot_guarded_candidate in SELECT.
  rewrite <-affine_zero_snapshot_complete_check_plan_tree in SELECT; fold plan yes in SELECT.
  change(clight_fragment_run fe(tree_statement(check_plan_tree plan)yes original)
    (Entry ge locals checked checked_memory)(FragmentObservation E0 old final Out_normal))in SELECT.
  destruct(proj1(@readonly_tree_execution_exact fe(check_plan_tree plan)yes original
    (Entry ge locals checked checked_memory)(FragmentObservation E0 old final Out_normal))SELECT)
    as [answer [CHECK BRANCH]].
  destruct(@check_plan_guarded_normal_execution fe ge locals checked checked_memory plan result live yes original
    answer old final CHECK YES NO PRIVATE BRANCH)as [target [EXECUTE FRAME]].
  exists target; split.
  - unfold affine_zero_snapshot_planned_captured_candidate; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
  - eapply temp_agree_trans; eassumption.
Qed.

Theorem affine_zero_snapshot_planned_observed_candidate_contract loads :
  source_observations_check(affine_inner_pointer_pointers package)loads=true ->
  PrivateRegion.projected_region_contract live(Ssequence(source_load_prefix loads)original)
    (Ssequence(source_load_prefix loads)affine_zero_snapshot_planned_captured_candidate).
Proof.
  intro CHECK; destruct(@source_observations_check_sound(affine_inner_pointer_pointers package)loads CHECK)as [COVER FRESH].
  apply source_prefix_region_contract with(writes:=source_load_targets loads++statement_temps original)
    (domain:=observed_pointer_domain(affine_inner_pointer_pointers package)).
  - apply source_load_prefix_supported.
  - apply writes_sequence.
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; left; exact MEMBER|apply source_load_prefix_writes].
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; right; exact MEMBER|].
      apply check_plan_frameable_writes; exact NO.
  - intros temps p locals entry memory middle after final PREFIX BODY.
    destruct(@source_load_prefix_observations loads(adapter_entry temps)(globalenv p)locals entry memory
      E0 middle memory Out_normal FRESH PREFIX)as [_ [_ [_ OBSERVED]]].
    intros identifier MEMBER; apply OBSERVED,COVER; exact MEMBER.
  - intros temps p locals entry memory after final SCOPE OBSERVED SOURCE.
    destruct(@affine_zero_snapshot_planned_captured_candidate_execution(adapter_entry temps)(globalenv p)locals entry memory
      after final OBSERVED SOURCE)as [target [EXECUTE PUBLIC]].
    exists target,final; split; [exact EXECUTE|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.
End REWRITE.

Print Assumptions affine_zero_snapshot_planned_captured_candidate_execution.
Print Assumptions affine_zero_snapshot_planned_observed_candidate_contract.
