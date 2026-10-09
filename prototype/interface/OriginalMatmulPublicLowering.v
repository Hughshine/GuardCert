
From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivatePool ClightTempFrame ClightTempFootprint ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl GuardMemoryDoubleMatmulNest
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulPipelineLoop GuardMemoryDoublePolyhedral
  GuardMemoryDoublePrepared GuardMemoryDoublePreparedAt GuardMemoryDoubleMatmulCapture GuardMemoryDoubleCandidateProgress
  GuardMemoryDoubleTensorBackend GuardMemoryDoubleNestedBackend GuardMemoryDoubleMatmulExit.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulNest Require Import OriginalMatmulNest.
From GuardOriginalMatmulPipeline Require Import OriginalMatmulPipeline.
From GuardOriginalMatmulPrepared Require Import OriginalMatmulPrepared.
From GuardOriginalMatmulCapture Require Import OriginalMatmulCapture.
From GuardOriginalMatmulCandidateProgress Require Import OriginalMatmulCandidateProgress.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardOriginalMatmulDoubleLowering Require Import OriginalMatmulDoubleLowering.
From GuardInterface Require Import OriginalMatmulPublicCapture.

(** The actual caller's live set is framed during lowering. Layout, ranges,
    capture resources and the checked generated Loop are unchanged. *)
Definition original_matmul_compile_for live (generated : DoubleAssignmentIRs.Loop.t) :=
  compile_double_tensor_loop original_matmul_double_layouts original_matmul_cache_layout
    original_matmul_candidate_bounds live original_matmul_scratch_pool (fst (fst generated)).
Theorem original_matmul_public_lowered_candidate_execution fe ge locals temps memory blocks generated code rows columns depth final live :
  double_matmul_static ge locals original_matmul_site blocks ->
  original_matmul_compile_for live generated=Some code ->
  0<=rows<=98 -> 0<=columns<=98 -> 0<=depth<=98 ->
  temps ! (matmul_capture_M original_matmul_captures)=Some (Vint (Int.repr rows)) ->
  temps ! (matmul_capture_N original_matmul_captures)=Some (Vint (Int.repr columns)) ->
  temps ! (matmul_capture_K original_matmul_captures)=Some (Vint (Int.repr depth)) ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) [rows;columns;depth]
    (RuntimeState (global_double_locations ge original_matmul_double_layouts) memory)
    (RuntimeState (global_double_locations ge original_matmul_double_layouts) final) ->
  exists target_temps, temp_agree (original_matmul_cache_layout++live) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps final Out_normal.
Proof.
  intros STATIC CODE MR NR KR M N K MODEL.
  destruct (@compile_double_tensor_loop_correct fe ge locals original_matmul_double_layouts
    (original_matmul_tensor_static STATIC) original_matmul_cache_layout original_matmul_candidate_bounds
    live original_matmul_scratch_pool (fst (fst generated)) code [rows;columns;depth] temps _ _ memory
    CODE (@original_matmul_cache_view temps rows columns depth MR NR KR M N K)
    (@original_matmul_bounds_view rows columns depth MR NR KR) MODEL
    ltac:(split; reflexivity)) as [target_temps [target_memory [[REG SAME] [FRAME RUN]]]].
  cbn [runtime_memory] in SAME; subst target_memory; exists target_temps; auto.
Qed.

Theorem original_matmul_public_guarded_candidate_execution fe ge locals temps memory blocks
  m_block n_block k_block body source_after source_final schedule swaps generated code live :
  (forall id, In id live -> ~ In id (double_matmul_capture_ids original_matmul_captures)) ->
  original_selected_body=Some body ->
  double_matmul_static ge locals original_matmul_site blocks ->
  double_global_binding ge locals _M m_block -> double_global_binding ge locals _N n_block ->
  double_global_binding ge locals _K k_block ->
  mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
  original_matmul_compile_for live generated=Some code ->
  exec_stmt fe ge locals temps memory body E0 source_after source_final Out_normal ->
  exists target_after, exec_stmt fe ge locals temps memory (original_matmul_guarded_code body code)
    E0 target_after source_final Out_normal /\ temp_agree live source_after target_after.
Proof.
  intros FRESH BODY STATIC MB NB KB PIPELINE CODE SOURCE.
  destruct (@original_matmul_public_capture_to_candidate_progress fe ge locals temps memory blocks original_matmul_double_layouts
    m_block n_block k_block body source_after source_final live FRESH BODY STATIC original_matmul_layout_certificate MB NB KB SOURCE)
    as [accepted [prepared [prepared_after [CAPTURE [FLAG [PUBLIC [FALLBACK [EXIT FACTS]]]]]]]].
  destruct accepted.
  - destruct (FACTS eq_refl) as [rows [columns [depth [MR [NR [KR [M [N [K [SET MODEL]]]]]]]]]].
    destruct (@original_matmul_public_lowered_candidate_execution fe ge locals prepared memory blocks generated code
      (Z.of_nat rows) (Z.of_nat columns) (Z.of_nat depth) source_final live STATIC CODE
      ltac:(lia) ltac:(lia) ltac:(lia) M N K (MODEL schedule swaps generated PIPELINE))
      as [candidate_after [FRAME CANDIDATE]].
    assert (CACHE_FRAME : temp_agree original_matmul_cache_layout prepared candidate_after).
    { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
    assert (PUBLIC_FRAME : temp_agree live prepared candidate_after).
    { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; apply in_or_app; right; exact MEMBER. }
    assert (RESTORE : exec_stmt fe ge locals candidate_after source_final
      (double_matmul_exit_code original_matmul_site original_matmul_captures) E0
      (double_matmul_nest_exit original_matmul_site rows columns depth candidate_after) source_final Out_normal).
    { apply double_matmul_exit_execution; [exact original_matmul_exit_fresh| | | | | |].
      - change (-2147483648<=Z.of_nat rows<=2147483647); lia.
      - change (-2147483648<=Z.of_nat columns<=2147483647); lia.
      - change (-2147483648<=Z.of_nat depth<=2147483647); lia.
      - rewrite (CACHE_FRAME _ (or_introl eq_refl)); exact M.
      - rewrite (CACHE_FRAME _ (or_intror (or_introl eq_refl))); exact N.
      - rewrite (CACHE_FRAME _ (or_intror (or_intror (or_introl eq_refl)))); exact K. }
    exists (double_matmul_nest_exit original_matmul_site rows columns depth candidate_after); split.
    + unfold original_matmul_guarded_code; eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0);
        [exact CAPTURE|].
      eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true); [constructor; exact FLAG|reflexivity|].
      eapply exec_Sseq_1 with (le1:=candidate_after) (m1:=source_final) (t1:=E0) (t2:=E0); eassumption.
    + eapply temp_agree_trans; [exact EXIT|rewrite SET; apply double_matmul_exit_frame; exact PUBLIC_FRAME].
  - exists prepared_after; split; [|exact EXIT].
    unfold original_matmul_guarded_code; eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0);
      [exact CAPTURE|].
    eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false); [constructor; exact FLAG|reflexivity|exact FALLBACK].
Qed.


Print Assumptions original_matmul_public_lowered_candidate_execution.
Print Assumptions original_matmul_public_guarded_candidate_execution.
