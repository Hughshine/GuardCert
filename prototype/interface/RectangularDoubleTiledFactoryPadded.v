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

From GuardInterface Require Import RectangularDoubleTiledFactory.

(** A pool may contain one unused private declaration after taking the
    per-axis caches. Candidate compilation still checks the returned pairs.
    Dropping a declaration neither creates an identifier nor changes its type. *)
Definition rectangular_counter_pairs (private : list (ident*type)) :=
  match private_counter_pairs private with
  | Some pairs=>Some pairs
  | None=>match private with _::rest=>private_counter_pairs rest | []=>None end end.

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
      | Some (caches,private)=>match rectangular_counter_pairs private with
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
  destruct (rectangular_counter_pairs private) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
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

Print Assumptions check_rectangular_tiled_double_region_sound.
