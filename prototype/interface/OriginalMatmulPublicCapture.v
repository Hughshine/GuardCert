From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightPrivatePool ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl GuardMemoryDoubleMatmulNest
  GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulPipelineLoop GuardMemoryDoublePolyhedral
  GuardMemoryDoubleMatmulCapture.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulNest Require Import OriginalMatmulNest.
From GuardOriginalMatmulPipeline Require Import OriginalMatmulPipeline.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardOriginalMatmulCapture Require Import OriginalMatmulCapture.
From GuardMemory Require Import GuardMemoryDoubleCandidateProgress.
From GuardOriginalMatmulPrepared Require Import OriginalMatmulPrepared.
From GuardOriginalMatmulCandidateProgress Require Import OriginalMatmulCandidateProgress.

(** Public scope belongs to the actual surrounding program. Only separation
    from the fixed capture resources is needed by this source instance. *)
Lemma original_matmul_public_capture_source_fresh live :
  (forall id, In id live -> ~ In id (double_matmul_capture_ids original_matmul_captures)) ->
  forall id, In id (statement_temps (double_matmul_source_nest original_matmul_site _M _N _K)++live) ->
  ~ In id (double_matmul_capture_ids original_matmul_captures).
Proof.
  intros FRESH id MEMBER; apply in_app_iff in MEMBER as [SOURCE|PUBLIC].
  - apply original_matmul_capture_source_fresh; apply in_or_app; left; exact SOURCE.
  - apply FRESH; exact PUBLIC.
Qed.
Theorem original_matmul_public_capture_and_source_model fe ge locals temps memory blocks layouts
  m_block n_block k_block body source_after source_final live :
  (forall id, In id live -> ~ In id (double_matmul_capture_ids original_matmul_captures)) ->
  original_selected_body=Some body ->
  double_matmul_static ge locals original_matmul_site blocks ->
  double_matmul_layout_certificate original_matmul_site layouts ->
  double_global_binding ge locals _M m_block -> double_global_binding ge locals _N n_block ->
  double_global_binding ge locals _K k_block ->
  exec_stmt fe ge locals temps memory body E0 source_after source_final Out_normal ->
  exists (accepted : bool) prepared prepared_after,
    exec_stmt fe ge locals temps memory original_matmul_capture_code E0 prepared memory Out_normal /\
    prepared ! (matmul_capture_flag original_matmul_captures)=Some (Vint (if accepted then Int.one else Int.zero)) /\
    temp_agree live temps prepared /\
    exec_stmt fe ge locals prepared memory body E0 prepared_after source_final Out_normal /\
    temp_agree live source_after prepared_after /\
    (accepted=true -> exists rows columns depth,
      Z.of_nat rows<=98 /\ Z.of_nat columns<=98 /\ Z.of_nat depth<=98 /\
      prepared ! (matmul_capture_M original_matmul_captures)=Some (Vint (Int.repr (Z.of_nat rows))) /\
      prepared ! (matmul_capture_N original_matmul_captures)=Some (Vint (Int.repr (Z.of_nat columns))) /\
      prepared ! (matmul_capture_K original_matmul_captures)=Some (Vint (Int.repr (Z.of_nat depth))) /\
      DoubleAssignmentIRs.Loop.loop_semantics (double_matmul_pipeline_nest original_matmul_site)
        [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]
        (RuntimeState (global_double_locations ge layouts) memory)
        (RuntimeState (global_double_locations ge layouts) source_final) /\
      prepared_after=double_matmul_nest_exit original_matmul_site rows columns depth prepared).
Proof.
  intros FRESH BODY STATIC LAYOUT MB NB KB SOURCE.
  pose proof BODY as SELECTED; rewrite original_selected_nest_exact in SELECTED; inversion SELECTED; subst body.
  destruct original_matmul_capture_resources as [DISTINCT PRIVATE].
  destruct (@double_matmul_source_capture fe ge locals temps memory original_matmul_site original_matmul_captures
    _M _N _K m_block n_block k_block 98 source_after source_final MB NB KB
    ltac:(change (0<=98<=2147483647); lia) DISTINCT PRIVATE SOURCE)
    as [accepted [prepared [CAPTURE [FLAG FACTS]]]].
  destruct (@double_matmul_capture_source_transport fe ge locals temps memory original_matmul_site
    original_matmul_captures _M _N _K 98 live prepared source_after source_final
    (original_matmul_public_capture_source_fresh FRESH) CAPTURE SOURCE) as [prepared_after [PREPARED PUBLIC]].
  exists accepted,prepared,prepared_after; split; [exact CAPTURE|split; [exact FLAG|split]].
  - eapply double_matmul_capture_public_frame; [exact FRESH|exact CAPTURE].
  - split; [exact PREPARED|split; [exact PUBLIC|intro TRUE]].
    destruct (FACTS TRUE) as [rows [columns [depth [MR [NR [KR [MC [NC [KC INV]]]]]]]]].
    destruct (proj1 (@original_full_nest_pipeline_model fe ge locals prepared memory blocks layouts
      m_block n_block k_block rows columns depth prepared_after source_final _ BODY STATIC LAYOUT
      MB NB KB MR NR KR INV) PREPARED) as [MODEL EXIT].
    exists rows,columns,depth; repeat split; assumption.
Qed.

Theorem original_matmul_public_capture_to_candidate_progress fe ge locals temps memory blocks layouts
  m_block n_block k_block body source_after source_final live :
  (forall id, In id live -> ~ In id (double_matmul_capture_ids original_matmul_captures)) ->
  original_selected_body=Some body ->
  double_matmul_static ge locals original_matmul_site blocks ->
  double_matmul_layout_certificate original_matmul_site layouts ->
  double_global_binding ge locals _M m_block -> double_global_binding ge locals _N n_block ->
  double_global_binding ge locals _K k_block ->
  exec_stmt fe ge locals temps memory body E0 source_after source_final Out_normal ->
  exists (accepted : bool) prepared prepared_after,
    exec_stmt fe ge locals temps memory original_matmul_capture_code E0 prepared memory Out_normal /\
    prepared ! (matmul_capture_flag original_matmul_captures)=Some (Vint (if accepted then Int.one else Int.zero)) /\
    temp_agree live temps prepared /\
    exec_stmt fe ge locals prepared memory body E0 prepared_after source_final Out_normal /\
    temp_agree live source_after prepared_after /\
    (accepted=true -> exists rows columns depth,
      Z.of_nat rows<=98 /\ Z.of_nat columns<=98 /\ Z.of_nat depth<=98 /\
      prepared ! (matmul_capture_M original_matmul_captures)=Some (Vint (Int.repr (Z.of_nat rows))) /\
      prepared ! (matmul_capture_N original_matmul_captures)=Some (Vint (Int.repr (Z.of_nat columns))) /\
      prepared ! (matmul_capture_K original_matmul_captures)=Some (Vint (Int.repr (Z.of_nat depth))) /\
      prepared_after=double_matmul_nest_exit original_matmul_site rows columns depth prepared /\
      forall schedule swaps generated,
        mayReturn (checked_double_prepared_loop_progress schedule swaps original_matmul_pipeline_request) (Some generated) ->
        DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated))
          [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth]
          (RuntimeState (global_double_locations ge layouts) memory)
          (RuntimeState (global_double_locations ge layouts) source_final)).
Proof.
  intros FRESH BODY STATIC LAYOUT MB NB KB SOURCE.
  destruct (@original_matmul_public_capture_and_source_model fe ge locals temps memory blocks layouts
    m_block n_block k_block body source_after source_final live FRESH BODY STATIC LAYOUT MB NB KB SOURCE)
    as [accepted [prepared [prepared_after [CAPTURE [FLAG [FRAME [FALLBACK [PUBLIC FACTS]]]]]]]].
  exists accepted,prepared,prepared_after; split; [exact CAPTURE|split; [exact FLAG|split; [exact FRAME|]]].
  split; [exact FALLBACK|split; [exact PUBLIC|intro TRUE]].
  destruct (FACTS TRUE) as [rows [columns [depth [MR [NR [KR [MC [NC [KC [MODEL EXIT]]]]]]]]]].
  exists rows,columns,depth; split; [exact MR|split; [exact NR|split; [exact KR|]]].
  split; [exact MC|split; [exact NC|split; [exact KC|split; [exact EXIT|]]]].
  intros schedule swaps generated PIPELINE.
  apply (proj1 (@original_matmul_generated_progress_at schedule swaps generated
    [Z.of_nat rows;Z.of_nat columns;Z.of_nat depth] ge layouts memory source_final eq_refl PIPELINE)); exact MODEL.
Qed.

Print Assumptions original_matmul_public_capture_source_fresh.
Print Assumptions original_matmul_public_capture_and_source_model.
Print Assumptions original_matmul_public_capture_to_candidate_progress.
