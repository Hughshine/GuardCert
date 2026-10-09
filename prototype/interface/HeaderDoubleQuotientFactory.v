From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCountedLoop ClightTempFrame ClightTempFootprint ClightGlobalScope
  ClightProjectedExecution ClightScopedPrivateRegion ClightRegionProgress CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryDoubleNestedBackend GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestProgress GuardMemoryDoubleReductionNestEntry
  GuardMemoryDoubleReductionNestLowering GuardMemoryDoubleUniformPrepared GuardMemoryTiledCompiler
  GuardMemoryDoubleQuotientPrepared GuardMemoryDoubleQuotientLowering GuardMemoryDoubleReductionQuotientLowering
  GuardMemoryDoubleHeaderBounds GuardMemoryDoubleHeaderNestData GuardMemoryDoubleHeaderNestProgress
  GuardMemoryDoubleHeaderNestEntry GuardMemoryDoubleHeaderQuotientLowering.
From GuardInterface Require Import ClightCheckPlanFrame ReductionDoubleRegionFactory ReductionDoubleQuotientFactory.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The proposal is independent of correctness; the footprint checker decides acceptance. *)
Definition header_double_limit description :=
  double_header_instruction_limit (reduction_nest_instruction description).
Definition header_double_source_globals p source :=
  match checked_double_header_raw_nest p [] source with
  | Some description => double_reduction_public_globals description
  | None => [] end.
Definition header_double_progress_supported p source :=
  match checked_double_header_raw_nest p [] source with Some _ => true | None => false end.
Theorem header_double_progress_supported_sound p source :
  header_double_progress_supported p source=true -> exists MODEL : region_progress source, True.
Proof.
  unfold header_double_progress_supported.
  destruct (checked_double_header_raw_nest p [] source) as [description|] eqn:CHECK;
    [intros ACCEPT; eapply checked_double_header_raw_nest_region_progress; exact CHECK|discriminate].
Qed.

Theorem quotient_header_double_region_contract p source description cache flag quotient limit divisor live pairs
  phase adapt choices generated capture quotient_range code :
  checked_double_header_raw_nest p [] source=Some description ->
  double_header_nest_entry_bounds_check limit description=true ->
  double_reduction_layout_span_check description=true ->
  reduction_double_quotient_resources source description cache flag quotient live=true ->
  0<divisor -> compile_double_ceil_capture cache quotient limit divisor=Some (capture,quotient_range) ->
  mayReturn (checked_double_quotient_tiled_prepared_loop phase adapt choices limit divisor quotient
    (double_header_pipeline_request description)) (Some generated) ->
  compile_double_quotient_candidate (double_source_instruction_layouts (reduction_nest_instruction description))
    cache flag quotient limit quotient_range live pairs generated=Some code ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p)
    (double_reduction_public_globals description) source
    (double_reduction_quotient_guarded_code source description cache flag limit capture code).
Proof.
  intros CHECK BOUNDS SPAN RESOURCES POSITIVE QUOTIENT PIPELINE CODE.
  destruct (DoubleNested.N.fresh_names_sound _ _ RESOURCES) as [NODUP FRESH].
  repeat rewrite NoDup_cons_iff in NODUP; cbn in NODUP.
  assert (DISTINCT : cache<>flag) by (intro SAME; subst flag; tauto).
  assert (CACHE_FRESH : ~ In cache (reduction_nest_iterators description)).
  { intro MEMBER; apply (FRESH cache ltac:(cbn; auto)), in_or_app; right; exact MEMBER. }
  assert (PRIVATE : forall key, In key (statement_temps source++live) -> ~ In key [cache;flag]).
  { intros key PUBLIC PRIVATE; apply (FRESH key ltac:(cbn in *; tauto)); apply in_or_app; left; exact PUBLIC. }
  assert (QFRESH : ~ In quotient (cache::flag::live)).
  { intros [SAME|[SAME|MEMBER]]; try (subst quotient; tauto).
    apply (FRESH quotient ltac:(cbn; auto)), in_or_app; left; apply in_or_app; right; exact MEMBER. }
  intros temps reference locals le tle memory after final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv reference) locals le memory
    source E0 after final Out_normal SOURCE live tle (statement_temps source)
    (@check_plan_frameable_writes source (@checked_double_header_raw_frameable p [] source description CHECK))
    SCOPE FRAME) as [transported [TRANSPORT FRAME_OUT]].
  destruct (@checked_double_header_quotient_guarded_execution p source description limit divisor phase adapt choices
    generated cache flag quotient live pairs capture quotient_range code (adapter_entry temps)
    (globalenv reference) locals tle memory transported final CHECK BOUNDS GLOBAL
    (@checked_double_header_public_scope p [] source description locals CHECK LOCAL)
    (@double_reduction_layout_span_check_sound description (globalenv reference) locals SPAN LOCAL)
    DISTINCT CACHE_FRESH PRIVATE QFRESH POSITIVE QUOTIENT PIPELINE CODE TRANSPORT)
    as [target_after [TARGET FRAME_TARGET]].
  exists target_after,final; split; [apply normal_fragment_steps; exact TARGET|].
  split; [eapply temp_agree_trans; eauto|apply memory_equivalent_refl].
Qed.

(** A caller supplies marked C and policy data. Freshness, actual safe capture,
    conditional validation, execution and public exits are internal to this factory. *)
Definition check_quotient_header_double_region p live pool phase adapt choices divisor source : Base.imp (option statement) :=
  match checked_double_reduction_raw_nest p [] source with
  | Some _ => pure None
  | None =>
  match pool,checked_double_header_raw_nest p [] source with
  | (cache,cache_type)::(flag,flag_type)::private,Some description =>
    if type_eq cache_type type_int32s then if type_eq flag_type type_int32s then
      match private_counter_pairs private with
      | Some ((quotient,reserved)::pairs) =>
        let limit := header_double_limit description in
        if 0<?divisor then
        if double_header_nest_entry_bounds_check limit description then
        if double_reduction_layout_span_check description then
        if reduction_double_quotient_resources source description cache flag quotient live then
          match compile_double_ceil_capture cache quotient limit divisor with
          | Some (capture,quotient_range) =>
            BIND generated <- checked_double_quotient_tiled_prepared_loop phase adapt choices limit divisor quotient
              (double_header_pipeline_request description) -;
            pure (match generated with
              | Some generated => match compile_double_quotient_candidate
                  (double_source_instruction_layouts (reduction_nest_instruction description))
                  cache flag quotient limit quotient_range live pairs generated with
                | Some code => Some (double_reduction_quotient_guarded_code source description cache flag limit capture code)
                | None => None end
              | None => None end)
          | None => pure None end
        else pure None else pure None else pure None else pure None
      | _ => pure None end
    else pure None else pure None
  | _,_ => pure None end end.
Theorem check_quotient_header_double_region_sound p live pool phase adapt choices divisor source target :
  mayReturn (check_quotient_header_double_region p live pool phase adapt choices divisor source) (Some target) ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p)
    (header_double_source_globals p source) source target.
Proof.
  unfold check_quotient_header_double_region,header_double_source_globals.
  destruct (checked_double_reduction_raw_nest p [] source);
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct pool as [|[cache cache_type] pool];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct pool as [|[flag flag_type] private];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (checked_double_header_raw_nest p [] source) as [description|] eqn:CHECK;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq cache_type type_int32s), (type_eq flag_type type_int32s);
    try (intro RUN; apply mayReturn_pure in RUN; discriminate).
  destruct (private_counter_pairs private) as [pairs|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct pairs as [|[quotient reserved] pairs];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (0<?divisor) eqn:POSITIVE; [apply Z.ltb_lt in POSITIVE|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_header_nest_entry_bounds_check (header_double_limit description) description) eqn:BOUNDS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_reduction_layout_span_check description) eqn:SPAN;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (reduction_double_quotient_resources source description cache flag quotient live) eqn:FRESH;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_double_ceil_capture cache quotient (header_double_limit description) divisor)
    as [[capture quotient_range]|] eqn:QUOTIENT;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated PIPELINE.
  destruct generated as [generated|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (compile_double_quotient_candidate
    (double_source_instruction_layouts (reduction_nest_instruction description)) cache flag quotient
    (header_double_limit description) quotient_range live pairs generated) as [code|] eqn:CODE;
    apply mayReturn_pure in RUN; [|discriminate].
  inversion RUN; subst target; eapply quotient_header_double_region_contract; eauto.
Qed.


Print Assumptions header_double_progress_supported_sound.
Print Assumptions quotient_header_double_region_contract.
Print Assumptions check_quotient_header_double_region_sound.
