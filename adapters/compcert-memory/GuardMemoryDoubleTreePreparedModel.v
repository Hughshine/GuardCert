From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution
  ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceTreeDecode GuardMemoryDoubleSourceTreeEffects GuardMemoryDoubleSourceTreeCertificates
  GuardMemoryDoubleSourceTreeSyntax GuardMemoryDoubleSourceTreeState GuardMemoryDoubleSourceTreeModelData
  GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleSourceTreeExit GuardMemoryDoubleSourceTreeCorrespondence
  GuardMemoryDoubleTreeCaptureLicense GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCaptureReceipt GuardMemoryDoubleTreeCaptureSource
  GuardMemoryDoubleTreeCapturePrepared GuardMemoryDoubleTreeCacheFrame GuardMemoryDoubleTreeCacheParameters
  GuardMemoryDoubleTreeProfileBounds GuardMemoryDoubleTreeCacheEnvironment GuardMemoryDoubleTreeFootprint
  GuardMemoryDoubleAffineBoxBounds GuardMemoryLongRangeCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** All dynamic range, active-header and leaf-location premises of the existing
    source/Loop bridge are now derived. Inputs are original syntax, checked
    profiles/footprints, allocation data and language/site scope receipts. *)
Theorem checked_double_tree_prepared_model p source tree fe ge locals temps memory after final live cache flag lower upper :
  checked_double_source_tree p source=Some tree -> preserving_globals (globalenv p) ge ->
  double_source_tree_scope tree locals -> locals_avoid (double_source_tree_headers tree) locals ->
  double_tree_footprint_check tree upper []=true ->
  (forall header, In header (double_source_tree_headers tree) ->
    Int.min_signed<=lower header<=Int.max_signed /\ Int.min_signed<=upper header<=Int.max_signed) ->
  double_tree_cache_distinct (double_source_tree_headers tree) cache ->
  (forall header, In header (double_source_tree_headers tree) -> cache header<>flag) ->
  (forall key, In key (statement_temps source++live) -> ~ In key (double_tree_capture_private tree cache flag)) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists prepared accepted prepared_after,
    exec_stmt fe ge locals temps memory (double_tree_capture_prepare tree cache flag lower upper) E0 prepared memory Out_normal /\
    double_tree_flag_value prepared flag accepted /\ temp_agree live temps prepared /\
    double_tree_cache_environment (double_source_tree_parameters tree) cache lower upper prepared /\
    exec_stmt fe ge locals prepared memory source E0 prepared_after final Out_normal /\ temp_agree live after prepared_after /\
    (accepted=true ->
      SL.loop_semantics (double_source_tree_model (double_source_tree_parameters tree) O tree)
        (double_tree_cached_parameters tree cache prepared)
        (RuntimeState (global_double_locations ge (double_source_tree_layouts tree)) memory)
        (RuntimeState (global_double_locations ge (double_source_tree_layouts tree)) final) /\
      prepared_after=double_source_tree_exit (double_tree_cached_value cache prepared) tree prepared).
Proof.
  intros DECODE GLOBAL SCOPE LOCAL FOOTPRINT LIMITS DISTINCT FRESH PRIVATE RUN.
  destruct (@checked_double_source_tree_sound p source tree DECODE) as [SOURCE [CHECK [WRITES LAYOUT]]].
  assert (EXCLUSIONS : double_source_tree_header_exclusions tree (double_source_tree_headers tree)).
  { intros instruction header POINT MEMBER; unfold double_tree_write_global.
    apply (@double_source_tree_header_writes_check_sound tree); [exact WRITES|exact POINT|].
    apply double_source_tree_parameter_membership; exact MEMBER. }
  set (initialized:=double_tree_initialized_temps (double_source_tree_parameters tree) cache temps).
  destruct (@double_tree_capture_source_licensed tree p [] fe ge locals (double_source_tree_headers tree)
    temps memory after final (PTree.set flag (Vint Int.one) initialized) memory cache flag lower upper true
    CHECK GLOBAL SCOPE EXCLUSIONS (incl_refl _) LOCAL LIMITS (double_tree_header_loads_refl ge _ memory)
    (PTree.gss _ _ _) ltac:(rewrite <- SOURCE; exact RUN)) as [prepared [accepted RECEIPT]].
  assert (CAPTURE : exec_stmt fe ge locals (PTree.set flag (Vint Int.one) initialized) memory
    (double_tree_capture_code tree cache flag lower upper) E0 prepared memory Out_normal).
  { apply (@double_tree_capture_receipt_execution ge locals memory cache flag lower upper tree _ prepared accepted RECEIPT);
      intros header MEMBER SAME; apply (FRESH header MEMBER); congruence. }
  assert (PREPARATION : exec_stmt fe ge locals temps memory (double_tree_capture_prepare tree cache flag lower upper)
    E0 prepared memory Out_normal).
  { unfold double_tree_capture_prepare; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    - apply double_tree_initialize_execution.
    - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [apply memory_capture_flag_execution|exact CAPTURE]. }
  assert (AGREE : temp_agree (statement_temps source++live) temps prepared).
  { intros key MEMBER; eapply writes_only_frame; [exact PREPARATION|apply double_tree_prepare_writes|apply PRIVATE; exact MEMBER]. }
  assert (ENV : double_tree_cache_environment (double_source_tree_headers tree) cache lower upper prepared).
  { apply (@double_tree_capture_environment_preserved ge locals memory cache flag lower upper tree _ prepared accepted
      RECEIPT (double_source_tree_headers tree) (incl_refl _) DISTINCT FRESH).
    intros header MEMBER; exists Int.zero; split.
    - rewrite PTree.gso by (apply FRESH; exact MEMBER); unfold initialized.
      apply double_tree_initialized_zero,double_source_tree_parameter_membership; exact MEMBER.
    - unfold double_tree_cache_interval; change (Z.min 0 (lower header)<=0<=Z.max 0 (upper header)).
      split; [apply Z.le_min_l|apply Z.le_max_l]. }
  destruct (@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal RUN
    (statement_temps source++live) prepared (double_source_tree_writes tree)
    ltac:(rewrite SOURCE; exact (@double_source_tree_writes_only p [] tree CHECK))
    ltac:(unfold statement_scope; intros key MEMBER; apply in_or_app; left; exact MEMBER) AGREE)
    as [prepared_after [REPLAY EXIT]].
  exists prepared,accepted,prepared_after; split; [exact PREPARATION|split; [exact (double_tree_capture_receipt_flag RECEIPT)|]].
  split; [eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact AGREE]|].
  split; [intros header MEMBER; apply ENV,double_source_tree_parameter_membership; exact MEMBER|].
  split; [exact REPLAY|split; [eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact EXIT]|]].
  intro ACCEPT.
  destruct (@double_tree_accepted_cached_headers ge locals memory cache flag lower upper tree _ prepared accepted
    RECEIPT DISTINCT FRESH ACCEPT) as [HEADERS RANGES].
  pose proof (@double_tree_capture_cached_profile ge locals memory cache flag lower upper tree _ prepared accepted
    RECEIPT DISTINCT FRESH ACCEPT) as PROFILE.
  assert (FACTS : double_source_tree_model_facts tree [] (double_tree_cached_value cache prepared) (fun _=>0)
    ge (double_source_tree_layouts tree)).
  { eapply double_tree_footprint_model_facts; [exact CHECK| |exact GLOBAL|exact SCOPE|exact FOOTPRINT|constructor| |exact RANGES].
    - intros instruction MEMBER; eapply checked_double_source_tree_layout_certificate; eassumption.
    - intros header MEMBER; exact (proj2 (PROFILE header MEMBER)). }
  exact (proj1 (@checked_double_source_tree_source_Loop p source tree (double_tree_cached_value cache prepared)
    fe ge locals prepared memory prepared_after final DECODE GLOBAL SCOPE FACTS HEADERS) REPLAY).
Qed.

Print Assumptions checked_double_tree_prepared_model.
