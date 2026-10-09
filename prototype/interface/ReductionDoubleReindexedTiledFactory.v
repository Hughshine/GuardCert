From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCountedLoop ClightTempFrame ClightTempFootprint ClightGlobalScope
  ClightProjectedExecution ClightScopedPrivateRegion ClightRegionProgress CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryDoubleNestedBackend GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestProgress
  GuardMemoryDoubleReductionNestEntry GuardMemoryDoubleReductionNestLowering
  GuardMemoryDoubleUniformPrepared GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightCheckPlanFrame ReductionDoubleRegionFactory.
From GuardMemory Require Import GuardMemoryDoubleTiledPrepared GuardMemoryDoubleReductionTiledLowering
  GuardMemoryDoubleReindexedTiledPrepared GuardMemoryDoubleReductionReindexedTiledLowering.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem reindexed_tiled_reduction_double_region_contract p source description cache flag limit live pairs
  phase adapt choices generated code :
  checked_double_reduction_raw_nest p [] source=Some description ->
  double_reduction_entry_bounds_check limit description=true ->
  double_reduction_layout_span_check description=true ->
  reduction_double_resources source description cache flag live=true ->
  mayReturn (checked_double_reindexed_tiled_prepared_loop_progress phase adapt choices limit
    (double_reduction_pipeline_request description)) (Some generated) ->
  compile_double_reduction_candidate description cache flag limit live pairs generated=Some code ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p)
    (double_reduction_public_globals description) source
    (double_reduction_guarded_code source description cache flag limit code).
Proof.
  intros CHECK BOUNDS SPAN RESOURCES PIPELINE CODE.
  destruct (DoubleNested.N.fresh_names_sound _ _ RESOURCES) as [NODUP FRESH].
  assert (DISTINCT : cache<>flag).
  { inversion NODUP as [|head tail HEAD TAIL]; subst.
    intro SAME; subst flag; apply HEAD; cbn; auto. }
  assert (CACHE_FRESH : ~ In cache (reduction_nest_iterators description)).
  { intro MEMBER; apply (FRESH cache ltac:(cbn; auto)).
    apply in_or_app; right; exact MEMBER. }
  assert (PRIVATE : forall key, In key (statement_temps source++live) -> ~ In key [cache;flag]).
  { intros key PUBLIC PRIVATE; apply (FRESH key PRIVATE); apply in_or_app; left; exact PUBLIC. }
  intros temps reference locals le tle memory after final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv reference) locals le memory
    source E0 after final Out_normal SOURCE live tle (statement_temps source)
    (@check_plan_frameable_writes source
      (@checked_double_reduction_raw_frameable p [] source description CHECK)) SCOPE FRAME)
    as [transported [TRANSPORT FRAME_OUT]].
  destruct (@checked_double_reindexed_tiled_reduction_guarded_execution p source description limit phase adapt
    choices generated cache flag live pairs code (adapter_entry temps) (globalenv reference) locals tle memory transported
    final CHECK BOUNDS GLOBAL (@checked_double_reduction_public_scope p [] source description
      locals CHECK LOCAL) (@double_reduction_layout_span_check_sound description (globalenv reference) locals SPAN LOCAL)
    DISTINCT CACHE_FRESH PRIVATE PIPELINE CODE TRANSPORT) as [target_after [TARGET FRAME_TARGET]].
  exists target_after,final; split.
  - apply normal_fragment_steps; exact TARGET.
  - split; [eapply temp_agree_trans; eauto|apply memory_equivalent_refl].
Qed.

(** Only data callbacks and actual checked source metadata enter this factory.
    All source/model, check, frame and public-exit obligations are internal. *)
Definition check_reindexed_tiled_reduction_double_region p live pool phase adapt choices source : Base.imp (option statement) :=
  match pool,checked_double_reduction_raw_nest p [] source with
  | (cache,cache_type)::(flag,flag_type)::private,Some description =>
    if type_eq cache_type type_int32s then if type_eq flag_type type_int32s then
      match private_counter_pairs private with
      | Some pairs =>
        let limit := reduction_double_limit description in
        if double_reduction_entry_bounds_check limit description then
        if double_reduction_layout_span_check description then
        if reduction_double_resources source description cache flag live then
          BIND generated <- checked_double_reindexed_tiled_prepared_loop_progress phase adapt choices limit
            (double_reduction_pipeline_request description) -;
          pure (match generated with
            | Some generated => match compile_double_reduction_candidate description cache flag limit live pairs generated with
              | Some code => Some (double_reduction_guarded_code source description cache flag limit code)
              | None => None end
            | None => None end)
        else pure None else pure None else pure None
      | None => pure None end
    else pure None else pure None
  | _,_ => pure None end.
Theorem check_reindexed_tiled_reduction_double_region_sound p live pool phase adapt choices source target :
  mayReturn (check_reindexed_tiled_reduction_double_region p live pool phase adapt choices source) (Some target) ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p)
    (reduction_double_source_globals p source) source target.
Proof.
  unfold check_reindexed_tiled_reduction_double_region,reduction_double_source_globals.
  destruct pool as [|[cache cache_type] pool];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct pool as [|[flag flag_type] private];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (checked_double_reduction_raw_nest p [] source) as [description|] eqn:CHECK;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq cache_type type_int32s), (type_eq flag_type type_int32s);
    try (intro RUN; apply mayReturn_pure in RUN; discriminate).
  destruct (private_counter_pairs private) as [pairs|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_reduction_entry_bounds_check (reduction_double_limit description) description) eqn:BOUNDS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_reduction_layout_span_check description) eqn:SPAN;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (reduction_double_resources source description cache flag live) eqn:FRESH;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated PIPELINE.
  destruct generated as [generated|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (compile_double_reduction_candidate description cache flag (reduction_double_limit description)
    live pairs generated) as [code|] eqn:CODE; apply mayReturn_pure in RUN; [|discriminate].
  inversion RUN; subst target; eapply reindexed_tiled_reduction_double_region_contract; eauto.
Qed.


Print Assumptions reindexed_tiled_reduction_double_region_contract.
Print Assumptions check_reindexed_tiled_reduction_double_region_sound.
