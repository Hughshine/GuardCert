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

From Guard Require Import ClightSkipPrefix.
From GuardInterface Require Import OriginalMatmulProgramBindings OriginalMatmulRawSource OriginalMatmulRawEquivalence.

Theorem original_matmul_raw_scoped_contract schedule swaps generated code :
  mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
  original_matmul_compile_candidate generated=Some code ->
  ScopedPrivateRegion.projected_region_contract (program_temps prog) (globalenv prog) original_matmul_globals
    raw_original_matmul_region (original_matmul_guarded_code raw_original_matmul_region code).
Proof.
  intros PIPELINE CODE temps p locals le tle memory source_after source_final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  apply original_matmul_raw_source_execution in SOURCE.
  unfold statement_scope in SCOPE.
  rewrite original_matmul_raw_temporary_footprint in SCOPE.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory
    original_matmul_region E0 source_after source_final Out_normal SOURCE (program_temps prog) tle
    [_i;_j;_k__1] original_matmul_writes SCOPE FRAME) as [transported [TRANSPORT FRAME_OUT]].
  destruct (@original_matmul_checked_guarded_execution (adapter_entry temps) (globalenv p) locals tle memory
    original_matmul_region transported source_final schedule swaps generated code GLOBAL LOCAL
    original_selected_region_exact PIPELINE CODE TRANSPORT) as [target_after [TARGET FRAME_TARGET]].
  apply original_matmul_raw_guarded_execution in TARGET.
  exists target_after,source_final; split.
  - apply normal_fragment_steps; exact TARGET.
  - split; [eapply temp_agree_trans; eauto|apply memory_equivalent_refl].
Qed.

Print Assumptions original_matmul_raw_scoped_contract.
