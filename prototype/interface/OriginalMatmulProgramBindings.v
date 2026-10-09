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

Definition original_matmul_declarations : list (ident * type) :=
  [(_A,double_tensor_type [100;100]);(_B,double_tensor_type [100;100]);
   (_C,double_tensor_type [100;100]);(_alpha,memory_double_type);(_beta,memory_double_type);
   (_M,memory_long_type);(_N,memory_long_type);(_K,memory_long_type)].
Definition original_matmul_globals := var_names original_matmul_declarations.
Lemma original_matmul_declarations_checked :
  global_declarations_check prog original_matmul_declarations=true.
Proof. vm_compute; reflexivity. Qed.
Lemma original_matmul_globals_checked : program_avoids_check original_matmul_globals prog=true.
Proof. vm_compute; reflexivity. Qed.
Lemma original_matmul_program_avoids : program_avoids original_matmul_globals prog.
Proof. apply program_avoids_check_sound; exact original_matmul_globals_checked. Qed.

Theorem original_matmul_checked_static ge locals :
  preserving_globals (globalenv prog) ge -> locals_avoid original_matmul_globals locals ->
  exists blocks m_block n_block k_block,
    double_matmul_static ge locals original_matmul_site blocks /\
    double_global_binding ge locals _M m_block /\ double_global_binding ge locals _N n_block /\
    double_global_binding ge locals _K k_block.
Proof.
  intros GLOBAL LOCAL.
  assert (LOOKUP : forall identifier expected, In (identifier,expected) original_matmul_declarations ->
    exists block, double_global_binding ge locals identifier block).
  { intros identifier expected MEMBER; eapply checked_global_binding;
      [exact original_matmul_declarations_checked|exact MEMBER|exact GLOBAL|exact LOCAL]. }
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

Theorem original_matmul_checked_guarded_execution fe ge locals temps memory body source_after source_final
  schedule swaps generated code :
  preserving_globals (globalenv prog) ge -> locals_avoid original_matmul_globals locals ->
  original_selected_body=Some body ->
  mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
  original_matmul_compile_candidate generated=Some code ->
  exec_stmt fe ge locals temps memory body E0 source_after source_final Out_normal ->
  exists target_after, exec_stmt fe ge locals temps memory (original_matmul_guarded_code body code)
    E0 target_after source_final Out_normal /\ temp_agree (program_temps prog) source_after target_after.
Proof.
  intros GLOBAL LOCAL BODY PIPELINE CODE SOURCE.
  destruct (original_matmul_checked_static GLOBAL LOCAL) as [blocks [m [n [k [STATIC [MB [NB KB]]]]]]].
  eapply original_matmul_guarded_candidate_execution; eauto.
Qed.

Lemma original_matmul_writes : writes_only [_i;_j;_k__1] original_matmul_region.
Proof. unfold original_matmul_region,original_long_loop; repeat constructor; cbn; tauto. Qed.

Theorem original_matmul_scoped_contract schedule swaps generated code :
  mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
  original_matmul_compile_candidate generated=Some code ->
  ScopedPrivateRegion.projected_region_contract (program_temps prog) (globalenv prog) original_matmul_globals
    original_matmul_region (original_matmul_guarded_code original_matmul_region code).
Proof.
  intros PIPELINE CODE temps p locals le tle memory source_after source_final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory
    original_matmul_region E0 source_after source_final Out_normal SOURCE (program_temps prog) tle
    [_i;_j;_k__1] original_matmul_writes SCOPE FRAME) as [transported [TRANSPORT FRAME_OUT]].
  destruct (@original_matmul_checked_guarded_execution (adapter_entry temps) (globalenv p) locals tle memory
    original_matmul_region transported source_final schedule swaps generated code GLOBAL LOCAL
    original_selected_region_exact PIPELINE CODE TRANSPORT) as [target_after [TARGET FRAME_TARGET]].
  exists target_after,source_final; split.
  - apply normal_fragment_steps; exact TARGET.
  - split; [eapply temp_agree_trans; eauto|apply memory_equivalent_refl].
Qed.

Print Assumptions original_matmul_program_avoids.
Print Assumptions original_matmul_checked_static.
Print Assumptions original_matmul_checked_guarded_execution.
Print Assumptions original_matmul_scoped_contract.
