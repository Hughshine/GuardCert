From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCountedLoop ClightTempFrame ClightTempFootprint ClightGlobalScope
  ClightProjectedExecution ClightScopedPrivateRegion ClightRegionProgress CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryDoubleNestedBackend GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleInitializedReductionData GuardMemoryDoubleInitializedRawNest
  GuardMemoryDoubleInitializedRawNestProgress GuardMemoryDoubleInitializedEntry
  GuardMemoryDoubleInitializedBounds GuardMemoryDoubleInitializedLayout
  GuardMemoryDoubleInitializedPipeline GuardMemoryDoubleInitializedLowering
  GuardMemoryDoubleUniformPrepared GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightCheckPlanFrame.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Search is a proposal; the final footprint checker is the authority.
    Neither maximality nor monotonicity is required for compiler correctness. *)
Fixpoint propose_initialized_double_limit fuel low high description :=
  match fuel with
  | O => low
  | S remaining =>
    let middle := (low+high+1)/2 in
    if double_initialized_entry_bounds_check middle description
    then propose_initialized_double_limit remaining middle high description
    else propose_initialized_double_limit remaining low (middle-1) description
  end.
Definition initialized_double_limit description :=
  propose_initialized_double_limit 32 0 Int.max_signed description.
Definition initialized_double_source_globals p source :=
  match checked_double_initialized_raw_nest p [] source with
  | Some (_,description) => double_initialized_public_globals description
  | None => [] end.
Definition initialized_double_resources source outers description cache flag live :=
  DoubleNested.N.fresh_names [cache;flag]
    ((statement_temps source++live)++outers++[initialized_reduction_iterator description]).

Theorem initialized_double_region_contract p source iterator rest description cache flag limit live pairs
  schedule swaps generated code :
  checked_double_initialized_raw_nest p [] source=Some (iterator::rest,description) ->
  double_initialized_entry_bounds_check limit description=true ->
  double_initialized_layout_span_check description=true ->
  initialized_double_resources source (iterator::rest) description cache flag live=true ->
  mayReturn (checked_double_uniform_prepared_loop_progress schedule swaps
    (double_initialized_pipeline_request (iterator::rest) description)) (Some generated) ->
  compile_double_initialized_candidate description cache flag limit live pairs generated=Some code ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p)
    (double_initialized_public_globals description) source
    (double_initialized_guarded_code source (iterator::rest) description cache flag limit code).
Proof.
  intros CHECK BOUNDS SPAN RESOURCES PIPELINE CODE.
  destruct (DoubleNested.N.fresh_names_sound _ _ RESOURCES) as [NODUP FRESH].
  assert (DISTINCT : cache<>flag).
  { inversion NODUP as [|head tail HEAD TAIL]; subst.
    intro SAME; subst flag; apply HEAD; cbn; auto. }
  assert (CACHE_FRESH : ~ In cache (iterator::rest++[initialized_reduction_iterator description])).
  { intro MEMBER; apply (FRESH cache ltac:(cbn; auto)).
    apply in_or_app; right; exact MEMBER. }
  assert (PRIVATE : forall key, In key (statement_temps source++live) -> ~ In key [cache;flag]).
  { intros key PUBLIC PRIVATE; apply (FRESH key PRIVATE); apply in_or_app; left; exact PUBLIC. }
  intros temps reference locals le tle memory after final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv reference) locals le memory
    source E0 after final Out_normal SOURCE live tle (statement_temps source)
    (@check_plan_frameable_writes source
      (@checked_double_initialized_raw_frameable p [] source (iterator::rest) description CHECK)) SCOPE FRAME)
    as [transported [TRANSPORT FRAME_OUT]].
  destruct (@checked_double_initialized_guarded_execution p source iterator rest description limit schedule swaps
    generated cache flag live pairs code (adapter_entry temps) (globalenv reference) locals tle memory transported
    final CHECK BOUNDS GLOBAL (@checked_double_initialized_public_scope p source (iterator::rest) description
      locals CHECK LOCAL) (@double_initialized_layout_span_check_sound description (globalenv reference) locals SPAN LOCAL)
    DISTINCT CACHE_FRESH PRIVATE PIPELINE CODE TRANSPORT) as [target_after [TARGET FRAME_TARGET]].
  exists target_after,final; split.
  - apply normal_fragment_steps; exact TARGET.
  - split; [eapply temp_agree_trans; eauto|apply memory_equivalent_refl].
Qed.

(** Only data callbacks and actual checked source metadata enter this factory.
    All source/model, check, frame and public-exit obligations are internal. *)
Definition check_initialized_double_region p live pool schedule swaps source : Base.imp (option statement) :=
  match pool,checked_double_initialized_raw_nest p [] source with
  | (cache,cache_type)::(flag,flag_type)::private,Some (iterator::rest,description) =>
    if type_eq cache_type type_int32s then if type_eq flag_type type_int32s then
      match private_counter_pairs private with
      | Some pairs =>
        let limit := initialized_double_limit description in
        if double_initialized_entry_bounds_check limit description then
        if double_initialized_layout_span_check description then
        if initialized_double_resources source (iterator::rest) description cache flag live then
          BIND generated <- checked_double_uniform_prepared_loop_progress schedule swaps
            (double_initialized_pipeline_request (iterator::rest) description) -;
          pure (match generated with
            | Some generated => match compile_double_initialized_candidate description cache flag limit live pairs generated with
              | Some code => Some (double_initialized_guarded_code source (iterator::rest) description cache flag limit code)
              | None => None end
            | None => None end)
        else pure None else pure None else pure None
      | None => pure None end
    else pure None else pure None
  | _,_ => pure None end.
Theorem check_initialized_double_region_sound p live pool schedule swaps source target :
  mayReturn (check_initialized_double_region p live pool schedule swaps source) (Some target) ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p)
    (initialized_double_source_globals p source) source target.
Proof.
  unfold check_initialized_double_region,initialized_double_source_globals.
  destruct pool as [|[cache cache_type] pool];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct pool as [|[flag flag_type] private];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (checked_double_initialized_raw_nest p [] source) as [[outers description]|] eqn:CHECK;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct outers as [|iterator rest]; [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (type_eq cache_type type_int32s), (type_eq flag_type type_int32s);
    try (intro RUN; apply mayReturn_pure in RUN; discriminate).
  destruct (private_counter_pairs private) as [pairs|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_initialized_entry_bounds_check (initialized_double_limit description) description) eqn:BOUNDS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_initialized_layout_span_check description) eqn:SPAN;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (initialized_double_resources source (iterator::rest) description cache flag live) eqn:FRESH;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated PIPELINE.
  destruct generated as [generated|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (compile_double_initialized_candidate description cache flag (initialized_double_limit description)
    live pairs generated) as [code|] eqn:CODE; apply mayReturn_pure in RUN; [|discriminate].
  inversion RUN; subst target; eapply initialized_double_region_contract; eauto.
Qed.

Definition initialized_double_progress_supported p source :=
  match checked_double_initialized_raw_nest p [] source with Some _ => true | None => false end.
Theorem initialized_double_progress_supported_sound p source :
  initialized_double_progress_supported p source=true -> exists MODEL : region_progress source, True.
Proof.
  unfold initialized_double_progress_supported.
  destruct (checked_double_initialized_raw_nest p [] source) as [[outers description]|] eqn:CHECK;
    [intros ACCEPT; eapply checked_double_initialized_raw_nest_region_progress; exact CHECK|discriminate].
Qed.

Print Assumptions initialized_double_region_contract.
Print Assumptions check_initialized_double_region_sound.
Print Assumptions initialized_double_progress_supported_sound.
