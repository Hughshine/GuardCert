From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCountedLoop ClightTempFrame ClightTempFootprint ClightGlobalScope
  ClightProjectedExecution ClightScopedPrivateRegion ClightRegionProgress CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryDoubleNestedBackend GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleReductionNestData
  GuardMemoryDoubleRectangularNestData GuardMemoryDoubleRectangularNestDecoder
  GuardMemoryDoubleRectangularNestProgress GuardMemoryDoubleRectangularNestEntry
  GuardMemoryDoubleRectangularNestCapture GuardMemoryDoubleRectangularCandidate
  GuardMemoryDoubleRectangularPrepared GuardMemoryDoubleRectangularLowering GuardMemoryRectangularCapture GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightCheckPlanFrame ReductionDoubleRegionFactory.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition rectangular_double_source_globals p source :=
  match checked_double_rectangular_raw_nest p [] source with
  | Some description=>double_rectangular_public_globals description
  | None=>[] end.
Definition rectangular_double_progress_supported p source :=
  match checked_double_rectangular_raw_nest p [] source with Some _=>true | None=>false end.
Theorem rectangular_double_progress_supported_sound p source :
  rectangular_double_progress_supported p source=true -> exists MODEL : region_progress source, True.
Proof.
  unfold rectangular_double_progress_supported.
  destruct (checked_double_rectangular_raw_nest p [] source) as [description|] eqn:CHECK;
    [intros ACCEPT; eapply checked_double_rectangular_raw_nest_region_progress; exact CHECK|discriminate].
Qed.
Definition rectangular_double_resources source description caches flag live :=
  DoubleNested.N.fresh_names (flag::caches)
    ((statement_temps source++live)++double_rectangular_iterators (rectangular_nest_axes description)).
Theorem rectangular_tiled_double_region_contract p source description caches flag caps steps live pairs
  phase adapt choices generated code :
  checked_double_rectangular_raw_nest p [] source=Some description ->
  double_rectangular_entry_bounds_check caps description=true -> double_rectangular_layout_span_check description=true ->
  rectangular_double_resources source description caches flag live=true ->
  double_rectangular_capture_steps (rectangular_nest_axes description) caches caps=Some steps ->
  mayReturn (checked_double_rectangular_tiled_prepared_loop_progress phase adapt choices caps
    (double_rectangular_pipeline_request description)) (Some generated) ->
  compile_double_rectangular_candidate (double_source_instruction_layouts (rectangular_nest_instruction description))
    caches flag caps live pairs generated=Some code ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p)
    (double_rectangular_public_globals description) source
    (double_rectangular_guarded_code source steps flag
      (double_rectangular_iterators (rectangular_nest_axes description)) caches code).
Proof.
  intros CHECK BOUNDS SPAN RESOURCES STEPS PIPELINE CODE.
  destruct (DoubleNested.N.fresh_names_sound _ _ RESOURCES) as [NODUP FRESH].
  apply NoDup_cons_iff in NODUP as [FLAG DISTINCT].
  assert (CACHES_FRESH : forall cache, In cache caches ->
    ~ In cache (double_rectangular_iterators (rectangular_nest_axes description))).
  { intros cache MEMBER WRITTEN; apply (FRESH cache ltac:(right; exact MEMBER)); apply in_or_app; right; exact WRITTEN. }
  assert (PRIVATE : forall key, In key (statement_temps source++live) -> ~ In key (flag::caches)).
  { intros key PUBLIC RESOURCE; apply (FRESH key RESOURCE); apply in_or_app; left; exact PUBLIC. }
  intros temps reference locals le tle memory after final GLOBAL LOCAL SCOPE FRAME SOURCE f k.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv reference) locals le memory
    source E0 after final Out_normal SOURCE live tle (statement_temps source)
    (@check_plan_frameable_writes source (@checked_double_rectangular_raw_frameable p [] source description CHECK))
    SCOPE FRAME) as [transported [TRANSPORT FRAME_OUT]].
  destruct (@checked_double_rectangular_guarded_execution p source description caps steps phase adapt choices generated
    caches flag live pairs code (adapter_entry temps) (globalenv reference) locals tle memory transported final
    CHECK BOUNDS GLOBAL (@checked_double_rectangular_public_scope p [] source description locals CHECK LOCAL)
    (@double_rectangular_layout_span_check_sound description (globalenv reference) locals SPAN LOCAL)
    STEPS DISTINCT FLAG CACHES_FRESH PRIVATE PIPELINE CODE TRANSPORT)
    as [target_after [TARGET FRAME_TARGET]].
  exists target_after,final; split; [apply normal_fragment_steps; exact TARGET|].
  split; [eapply temp_agree_trans; eauto|apply memory_equivalent_refl].
Qed.

Fixpoint take_rectangular_double_caches depth (pool : list (ident*type)) : option (list ident*list (ident*type)) :=
  match depth,pool with
  | O,_=>Some ([],pool)
  | S depth,(cache,cache_type)::pool=>if type_eq cache_type type_int32s then
      match take_rectangular_double_caches depth pool with
      | Some (caches,private)=>Some (cache::caches,private)
      | None=>None end else None
  | _,_=>None end.

(** Caps, scheduling and candidate adaptation are untrusted policy data.
    The supported C user supplies marked source; this factory constructs its
    capture, candidate contract, public exits and installation evidence. *)
Definition check_rectangular_tiled_double_region p live pool phase adapt choices
  (caps_proposal : double_rectangular_nest -> list Z) source : Base.imp (option statement) :=
  match checked_double_reduction_raw_nest p [] source with
  | Some _=>pure None
  | None=>match pool,checked_double_rectangular_raw_nest p [] source with
    | (flag,flag_type)::pool,Some description=>if type_eq flag_type type_int32s then
      match take_rectangular_double_caches (length (rectangular_nest_axes description)) pool with
      | Some (caches,private)=>match private_counter_pairs private with
        | Some pairs=>let caps := caps_proposal description in
          if double_rectangular_entry_bounds_check caps description then
          if double_rectangular_layout_span_check description then
          if rectangular_double_resources source description caches flag live then
            match double_rectangular_capture_steps (rectangular_nest_axes description) caches caps with
            | Some steps=>
              BIND generated <- checked_double_rectangular_tiled_prepared_loop_progress phase adapt choices caps
                (double_rectangular_pipeline_request description) -;
              pure (match generated with
                | Some generated=>match compile_double_rectangular_candidate
                    (double_source_instruction_layouts (rectangular_nest_instruction description)) caches flag caps live pairs generated with
                  | Some code=>Some (double_rectangular_guarded_code source steps flag
                      (double_rectangular_iterators (rectangular_nest_axes description)) caches code)
                  | None=>None end
                | None=>None end)
            | None=>pure None end
          else pure None else pure None else pure None
        | None=>pure None end
      | None=>pure None end else pure None
    | _,_=>pure None end end.
Theorem check_rectangular_tiled_double_region_sound p live pool phase adapt choices caps_proposal source target :
  mayReturn (check_rectangular_tiled_double_region p live pool phase adapt choices caps_proposal source) (Some target) ->
  ScopedPrivateRegion.projected_region_contract live (globalenv p)
    (rectangular_double_source_globals p source) source target.
Proof.
  unfold check_rectangular_tiled_double_region,rectangular_double_source_globals.
  destruct (checked_double_reduction_raw_nest p [] source);
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct pool as [|[flag flag_type] pool]; [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (checked_double_rectangular_raw_nest p [] source) as [description|] eqn:CHECK;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq flag_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (take_rectangular_double_caches (length (rectangular_nest_axes description)) pool)
    as [[caches private]|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs private) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_rectangular_entry_bounds_check (caps_proposal description) description) eqn:BOUNDS;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_rectangular_layout_span_check description) eqn:SPAN;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (rectangular_double_resources source description caches flag live) eqn:FRESH;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (double_rectangular_capture_steps (rectangular_nest_axes description) caches (caps_proposal description))
    as [steps|] eqn:STEPS; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN generated PIPELINE.
  destruct generated as [generated|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (compile_double_rectangular_candidate
    (double_source_instruction_layouts (rectangular_nest_instruction description)) caches flag
    (caps_proposal description) live pairs generated) as [code|] eqn:CODE;
    apply mayReturn_pure in RUN; [|discriminate].
  inversion RUN; subst target; eapply rectangular_tiled_double_region_contract; eauto.
Qed.

Print Assumptions rectangular_double_progress_supported_sound.
Print Assumptions rectangular_tiled_double_region_contract.
Print Assumptions check_rectangular_tiled_double_region_sound.
