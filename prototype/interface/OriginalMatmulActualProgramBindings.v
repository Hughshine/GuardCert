From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightTempFrame ClightTempFootprint ClightGlobalScope
  ClightCountedLoop ClightProjectedExecution ClightScopedPrivateRegion ClightRegionProgress CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleTensorBackend GuardMemoryDoubleProgramBindings
  GuardMemoryDoubleCandidateProgress.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulDoubleLowering Require Import OriginalMatmulDoubleLowering.
From GuardOriginalMatmulPipeline Require Import OriginalMatmulPipeline.
From GuardOriginalMatmulPrepared Require Import OriginalMatmulPrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

From Guard Require Import ClightSkipPrefix ClightPrivatePool.
From GuardInterface Require Import OriginalMatmulProgramBindings OriginalMatmulSelectedInstallation
  OriginalMatmulRawSource OriginalMatmulRawEquivalence OriginalMatmulPublicLowering.
From GuardOriginalMatmulCapture Require Import OriginalMatmulCapture.
From GuardMemory Require Import GuardMemoryDoubleMatmulCapture.

Theorem original_matmul_actual_static p ge locals :
  global_declarations_check p original_matmul_declarations=true ->
  preserving_globals (globalenv p) ge -> locals_avoid original_matmul_globals locals ->
  exists blocks m_block n_block k_block,
    double_matmul_static ge locals original_matmul_site blocks /\
    double_global_binding ge locals _M m_block /\ double_global_binding ge locals _N n_block /\
    double_global_binding ge locals _K k_block.
Proof.
  intros DECL GLOBAL LOCAL.
  assert (LOOKUP : forall identifier expected, In (identifier,expected) original_matmul_declarations ->
    exists block, double_global_binding ge locals identifier block).
  { intros identifier expected MEMBER; eapply checked_global_binding;
      [exact DECL|exact MEMBER|exact GLOBAL|exact LOCAL]. }
  destruct (LOOKUP _A (double_tensor_type [100;100]) ltac:(cbn; tauto)) as [a A].
  destruct (LOOKUP _B (double_tensor_type [100;100]) ltac:(cbn; tauto)) as [b B].
  destruct (LOOKUP _C (double_tensor_type [100;100]) ltac:(cbn; tauto)) as [c C].
  destruct (LOOKUP _alpha memory_double_type ltac:(cbn; tauto)) as [alpha ALPHA].
  destruct (LOOKUP _beta memory_double_type ltac:(cbn; tauto)) as [beta BETA].
  destruct (LOOKUP _M memory_long_type ltac:(cbn; tauto)) as [m MB].
  destruct (LOOKUP _N memory_long_type ltac:(cbn; tauto)) as [n NB].
  destruct (LOOKUP _K memory_long_type ltac:(cbn; tauto)) as [k KB].
  exists (DoubleMatmulBlocks a b c alpha beta),m,n,k; split; [|auto].
  constructor; try assumption.
  - change (-2147483648<=2<=2147483647); lia.
  - change (80000<=18446744073709551616); lia.
Qed.


Lemma original_matmul_actual_capture_fresh live :
  private_pool_check live original_matmul_private_pool=true ->
  forall id, In id live -> ~ In id (double_matmul_capture_ids original_matmul_captures).
Proof.
  intros CHECK id PUBLIC PRIVATE; eapply (@private_pool_check_sound live original_matmul_private_pool CHECK id PUBLIC).
  unfold original_matmul_private_pool,var_names; rewrite map_app; apply in_or_app; left.
  apply original_matmul_capture_pool_members; exact PRIVATE.
Qed.
Theorem original_matmul_actual_scoped_contract reference live schedule swaps generated code :
  global_declarations_check reference original_matmul_declarations=true ->
  private_pool_check live original_matmul_private_pool=true ->
  mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
  original_matmul_compile_for live generated=Some code ->
  ScopedPrivateRegion.projected_region_contract live (globalenv reference) original_matmul_globals
    raw_original_matmul_region (original_matmul_guarded_code raw_original_matmul_region code).
Proof.
  intros DECL PRIVATE PIPELINE CODE temps p locals le tle memory source_after source_final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  apply original_matmul_raw_source_execution in SOURCE.
  unfold statement_scope in SCOPE.
  rewrite original_matmul_raw_temporary_footprint in SCOPE.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory
    original_matmul_region E0 source_after source_final Out_normal SOURCE live tle
    [_i;_j;_k__1] original_matmul_writes SCOPE FRAME) as [transported [TRANSPORT FRAME_OUT]].
  destruct (@original_matmul_actual_static reference (globalenv p) locals DECL GLOBAL LOCAL)
    as [blocks [mb [nb [kb [STATIC [MB [NB KB]]]]]]].
  destruct (@original_matmul_public_guarded_candidate_execution (adapter_entry temps) (globalenv p) locals tle memory
    blocks mb nb kb original_matmul_region transported source_final schedule swaps generated code live
    (@original_matmul_actual_capture_fresh live PRIVATE) original_selected_region_exact STATIC MB NB KB PIPELINE CODE TRANSPORT)
    as [target_after [TARGET FRAME_TARGET]].
  apply original_matmul_raw_guarded_execution in TARGET.
  exists target_after,source_final; split.
  - apply normal_fragment_steps; exact TARGET.
  - split; [eapply temp_agree_trans; eauto|apply memory_equivalent_refl].
Qed.


Print Assumptions original_matmul_actual_static.
Print Assumptions original_matmul_actual_capture_fresh.
Print Assumptions original_matmul_actual_scoped_contract.
