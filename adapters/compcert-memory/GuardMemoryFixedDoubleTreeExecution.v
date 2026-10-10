From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightTempFrame ClightTempFootprint ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleSourceTransport
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeState GuardMemoryDoubleSourceTreeModelData GuardMemoryDoubleSourceTreeExit
  GuardMemoryDoublePipelineTransport GuardMemoryDoublePolyhedral GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleNestedBackend GuardMemoryDoubleTreeEntry GuardMemoryDoubleTreeGuarded
  GuardMemoryDoubleTreePrepared GuardMemoryDoubleTreeSourcePrepared GuardMemoryDoubleTreeCacheParameters
  GuardMemoryDoubleTreeCacheEnvironment GuardMemoryDoubleTreeExitCode GuardMemoryDoubleTreeResidualCandidate
  GuardMemoryFixedDoubleTreeData GuardMemoryFixedDoubleTreeDecode GuardMemoryFixedDoubleTreeSource
  GuardMemoryFixedDoubleTreeFacts GuardMemoryFixedDoubleTreeCache GuardMemoryFixedDoubleTreeScope.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition fixed_double_tree_pipeline_request tree : DoubleAssignmentIRs.Loop.t :=
  let model:=fixed_double_tree_skeleton tree in
  (double_pipeline_statement (double_source_tree_model (double_source_tree_parameters model) O model),
   double_source_tree_parameters model,map (fun key=>(key,tt)) (fixed_double_tree_public_globals tree)).
Definition fixed_double_tree_candidate_code tree cache code :=
  Ssequence (fixed_double_cache_code (double_source_tree_parameters (fixed_double_tree_skeleton tree)) cache)
    (Ssequence code (double_tree_exit_code (fixed_double_tree_skeleton tree) cache)).

(** All prerequisites are produced by static checks and host entry evidence.
    Source execution is the semantic proof starting point, not emitted work. *)
Theorem checked_fixed_double_tree_candidate_execution p source tree cache flag live pool phase adapt shifts choices generated code
  fe ge locals temps memory after final :
  checked_fixed_double_source_tree p source=Some tree -> preserving_globals (globalenv p) ge ->
  double_source_tree_scope (fixed_double_tree_skeleton tree) locals ->
  double_tensor_static ge locals (double_source_tree_layouts (fixed_double_tree_skeleton tree)) ->
  fixed_double_tree_footprint_check tree []=true ->
  double_tree_resources source (fixed_double_tree_skeleton tree) cache flag live=true ->
  mayReturn (checked_double_tree_source_prepared_loop_progress phase adapt shifts choices
    (double_tree_parameter_intervals (double_source_tree_parameters (fixed_double_tree_skeleton tree))
      fixed_double_parameter_value fixed_double_parameter_value) (fixed_double_tree_pipeline_request tree)) (Some generated) ->
  compile_residual_double_tree_candidate (double_source_tree_layouts (fixed_double_tree_skeleton tree))
    (fixed_double_tree_skeleton tree) cache flag fixed_double_parameter_value fixed_double_parameter_value live pool generated=Some code ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists target_after,
    exec_stmt fe ge locals temps memory (fixed_double_tree_candidate_code tree cache code)
      E0 target_after final Out_normal /\ temp_agree live after target_after.
Proof.
  intros CHECK GLOBAL SCOPE STATIC FOOTPRINT RESOURCES PIPELINE CODE SOURCE.
  destruct (@checked_fixed_double_source_tree_sound p source tree CHECK) as [SHAPE [TREE LAYOUT]].
  pose proof (@checked_fixed_double_tree_shared_layout p source tree CHECK) as SHARED.
  assert (FACTS : fixed_double_tree_facts tree [] (fun _=>0) ge
    (double_source_tree_layouts (fixed_double_tree_skeleton tree))).
  { eapply fixed_double_tree_footprint_model_facts;
      [exact TREE|exact SHARED|exact GLOBAL|exact SCOPE|exact FOOTPRINT|constructor]. }
  rewrite SHAPE in SOURCE.
  destruct (proj1 (@fixed_double_source_tree_source_Loop p tree [] (fun _=>0) fe ge locals
    (double_source_tree_layouts (fixed_double_tree_skeleton tree)) temps memory after final
    GLOBAL TREE SHARED SCOPE FACTS ltac:(intros identifier MEMBER; contradiction)) SOURCE) as [MODEL SET].
  unfold double_tree_resources in RESOURCES.
  destruct (DoubleNested.N.fresh_names_sound _ _ RESOURCES) as [DISTINCT PRIVATE].
  apply NoDup_cons_iff in DISTINCT as [FLAG CACHES].
  assert (RANGES : forall header, In header (double_source_tree_parameters (fixed_double_tree_skeleton tree)) ->
    Int.min_signed<=fixed_double_parameter_value header<=Int.max_signed).
  { intros header MEMBER; apply (@fixed_double_tree_header_ranges p [] tree TREE header).
    apply double_source_tree_parameter_membership; exact MEMBER. }
  set (prepared:=fixed_double_cache_temps (double_source_tree_parameters (fixed_double_tree_skeleton tree)) cache temps).
  assert (PREPARE : exec_stmt fe ge locals temps memory
    (fixed_double_cache_code (double_source_tree_parameters (fixed_double_tree_skeleton tree)) cache) E0 prepared memory Out_normal).
  { apply fixed_double_cache_execution. }
  assert (ENV : double_tree_cache_environment (double_source_tree_parameters (fixed_double_tree_skeleton tree))
    cache fixed_double_parameter_value fixed_double_parameter_value prepared).
  { apply fixed_double_cache_environment; assumption. }
  assert (PARAMETERS : double_tree_cached_parameters (fixed_double_tree_skeleton tree) cache prepared=
    map fixed_double_parameter_value (double_source_tree_parameters (fixed_double_tree_skeleton tree))).
  { unfold double_tree_cached_parameters; apply map_ext_in; intros header MEMBER.
    apply fixed_double_cache_values; assumption. }
  assert (CANDIDATE_MODEL : DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated))
    (double_tree_cached_parameters (fixed_double_tree_skeleton tree) cache prepared)
    (RuntimeState (global_double_locations ge (double_source_tree_layouts (fixed_double_tree_skeleton tree))) memory)
    (RuntimeState (global_double_locations ge (double_source_tree_layouts (fixed_double_tree_skeleton tree))) final)).
  { eapply (@checked_double_tree_source_prepared_loop_progress_at phase adapt shifts choices _
      (fixed_double_tree_pipeline_request tree) generated _ _ _ PIPELINE).
    - unfold fixed_double_tree_pipeline_request,double_tree_cached_parameters; cbn [fst snd]; rewrite map_length; reflexivity.
    - apply global_double_locations_nonalias.
    - apply double_tree_cached_parameter_ranges; exact ENV.
    - rewrite PARAMETERS; apply double_pipeline_execution; exact MODEL. }
  destruct (@compiled_residual_double_tree_candidate_execution
    (double_source_tree_layouts (fixed_double_tree_skeleton tree)) (fixed_double_tree_skeleton tree) cache flag
    fixed_double_parameter_value fixed_double_parameter_value live pool generated code fe ge locals prepared memory final
    STATIC CODE ENV CANDIDATE_MODEL) as [candidate_after [FRAME CANDIDATE]].
  assert (MEMBERSHIP : forall header, In header (double_source_tree_headers (fixed_double_tree_skeleton tree)) ->
    In header (double_source_tree_parameters (fixed_double_tree_skeleton tree))).
  { intros header MEMBER; apply double_source_tree_parameter_membership; exact MEMBER. }
  assert (CACHE_FRAME : forall header, In header (double_source_tree_headers (fixed_double_tree_skeleton tree)) ->
    candidate_after ! (cache header)=prepared ! (cache header)).
  { intros header MEMBER; apply FRAME; apply in_or_app; left; apply in_map,MEMBERSHIP; exact MEMBER. }
  assert (VALUES : forall header, In header (double_source_tree_headers (fixed_double_tree_skeleton tree)) ->
    double_tree_cached_value cache candidate_after header=fixed_double_parameter_value header).
  { intros header MEMBER; unfold double_tree_cached_value; rewrite CACHE_FRAME by exact MEMBER.
    change (double_tree_cached_value cache prepared header=fixed_double_parameter_value header).
    apply fixed_double_cache_values; [exact CACHES|exact RANGES|apply MEMBERSHIP; exact MEMBER]. }
  assert (CACHES_FRESH : forall header, In header (double_source_tree_headers (fixed_double_tree_skeleton tree)) ->
    ~ In (cache header) (double_source_tree_writes (fixed_double_tree_skeleton tree))).
  { intros header MEMBER WRITE; apply (PRIVATE (cache header));
      [right; apply in_map,MEMBERSHIP; exact MEMBER|apply in_or_app; right; exact WRITE]. }
  assert (RESTORE : exec_stmt fe ge locals candidate_after final
    (double_tree_exit_code (fixed_double_tree_skeleton tree) cache) E0
    (double_source_tree_exit (double_tree_cached_value cache candidate_after) (fixed_double_tree_skeleton tree) candidate_after)
    final Out_normal).
  { apply double_tree_exit_code_execution; [exact CACHES_FRESH|].
    intros header MEMBER; destruct (ENV header (MEMBERSHIP header MEMBER)) as [word [WORD RANGE]].
    exists word; rewrite CACHE_FRAME by exact MEMBER; exact WORD. }
  exists (double_source_tree_exit (double_tree_cached_value cache candidate_after) (fixed_double_tree_skeleton tree) candidate_after).
  split.
  - unfold fixed_double_tree_candidate_code.
    eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0); [exact PREPARE|].
    eapply exec_Sseq_1 with (le1:=candidate_after) (m1:=final) (t1:=E0) (t2:=E0); eassumption.
  - rewrite SET; unfold fixed_double_tree_exit.
    rewrite (@double_tree_exit_valuation_agree (fixed_double_tree_skeleton tree)
      fixed_double_parameter_value (double_tree_cached_value cache candidate_after) candidate_after VALUES).
    apply double_tree_exit_public_frame; eapply temp_agree_trans.
    + intros key MEMBER; apply fixed_double_cache_frame; intro BAD; apply (PRIVATE key).
      * right; exact BAD.
      * apply in_or_app; left; apply in_or_app; right; exact MEMBER.
    + eapply temp_agree_weaken; [|exact FRAME].
      intros key MEMBER; apply in_or_app; right; right; exact MEMBER.
Qed.
Print Assumptions checked_fixed_double_tree_candidate_execution.
