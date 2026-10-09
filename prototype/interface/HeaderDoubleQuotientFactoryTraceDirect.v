From Stdlib Require Import List Bool ZArith String.
From compcert.lib Require Import Coqlib Integers.
From compcert.cfrontend Require Import Ctypes Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure Debugging.
From Guard Require Import ClightTempFootprint.
From GuardMemory Require Import GuardMemoryDoubleNestedBackend GuardMemoryDoubleSourceInstruction
  GuardMemoryTiledCompiler
  GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestEntry GuardMemoryDoubleReductionQuotientLowering
  GuardMemoryDoubleQuotientPrepared GuardMemoryDoubleQuotientLowering GuardMemoryDoubleQuotientTrace
  GuardMemoryDoubleTiledPhaseTrace GuardMemoryDoubleHeaderNestData GuardMemoryDoubleHeaderNestEntry GuardMemoryDoubleHeaderBounds.
From GuardInterface Require Import ReductionDoubleRegionFactory ReductionDoubleQuotientFactory ReductionDoubleQuotientFactoryTrace HeaderDoubleQuotientFactory.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition traced_check_quotient_header_double_region p live pool phase adapt choices divisor source : Base.imp (option statement) :=
  match checked_double_reduction_raw_nest p [] source with
  | Some _ => pure None
  | None =>
  match pool,checked_double_header_raw_nest p [] source with
  | (cache,cache_type)::(flag,flag_type)::private,Some description =>
    if type_eq cache_type type_int32s then if type_eq flag_type type_int32s then
      match private_counter_pairs private with
      | Some ((quotient,reserved)::pairs) =>
        let limit := double_header_instruction_limit (reduction_nest_instruction description) in
        if 0<?divisor then
        if double_header_nest_entry_bounds_check limit description then
        if double_reduction_layout_span_check description then
        if reduction_double_quotient_resources source description cache flag quotient live then
          match compile_double_ceil_capture cache quotient limit divisor with
          | Some (capture,quotient_range) =>
            BIND generated <- traced_double_quotient_prepared_loop phase adapt choices limit divisor quotient
              (double_header_pipeline_request description) -;
            pure (match generated with
              | Some generated => match quotient_lowering_stage
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
Theorem traced_check_quotient_header_double_region_exact p live pool phase adapt choices divisor source :
  traced_check_quotient_header_double_region p live pool phase adapt choices divisor source =
  check_quotient_header_double_region p live pool phase adapt choices divisor source.
Proof.
  unfold traced_check_quotient_header_double_region,check_quotient_header_double_region,
    quotient_lowering_stage,traced_double_quotient_prepared_loop,checked_double_quotient_tiled_prepared_loop,
    header_double_limit,double_phase_stage,trace.
  reflexivity.
Qed.
Print Assumptions traced_check_quotient_header_double_region_exact.
