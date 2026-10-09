From Stdlib Require Import List String ZArith.
From polcert.src Require Import OpenScop TilingWitness.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure Debugging.
From GuardMemory Require Import GuardMemoryDoublePolyhedral GuardMemoryDoubleTiledPrepared
  GuardMemoryDoubleReindexedTiling GuardMemoryDoubleTiledPhaseTrace GuardMemoryDoubleNestedBackend
  GuardMemoryDoubleQuotientPrepared GuardMemoryDoubleQuotientLowering.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope string_scope.

Definition traced_double_quotient_prepared_loop phase
  (adapt : Z -> Z -> DBL.t -> result DBL.t) choices limit divisor quotient_name (source : DBL.t) :=
  BIND proposed <- double_phase_stage "quotient-raw"
    (fun _ => checked_double_tiled_prepared_loop phase source) -;
  match proposed with
  | None => trace INFO "guardcert-phase/quotient-raw/refused" (pure None)
  | Some (raw,witnesses) =>
    match double_phase_stage "quotient-adaptation"
      (fun _ => adapt limit divisor (double_extend_parameter quotient_name raw)) with
    | Err _ => trace INFO "guardcert-phase/quotient-adaptation/refused" (pure None)
    | Okk candidate =>
      let '((body,context),vars) := double_extend_parameter quotient_name source in
      let target := fst (fst candidate) in
      BIND valid <- double_phase_stage "quotient-final-validation"
        (fun _ => checked_double_reindexed_tiling_choices
          (double_quotient_assumed_loop limit divisor body,context,vars)
          (double_quotient_assumed_loop limit divisor target,context,vars)
          (map double_extend_tiling_witness witnesses) choices) -;
      if valid then trace INFO "guardcert-phase/quotient-final-validation/accepted"
        (pure (Some (target,context,vars)))
      else trace INFO "guardcert-phase/quotient-final-validation/refused" (pure None)
    end
  end.
Theorem traced_double_quotient_prepared_loop_exact phase adapt choices limit divisor quotient_name source :
  traced_double_quotient_prepared_loop phase adapt choices limit divisor quotient_name source =
  checked_double_quotient_tiled_prepared_loop phase adapt choices limit divisor quotient_name source.
Proof.
  unfold traced_double_quotient_prepared_loop,checked_double_quotient_tiled_prepared_loop,
    double_phase_stage,trace; reflexivity.
Qed.

Definition traced_double_quotient_candidate layouts cache flag quotient limit quotient_range live pool (generated : DBL.t) :=
  match double_phase_stage "quotient-lowering" (fun _ => compile_double_tensor_loop layouts
    [quotient;cache] [quotient_range;DoubleNested.A.Interval 0 limit] (flag::live) pool
    (fst (fst generated))) with
  | Some code => trace INFO "guardcert-phase/quotient-lowering/accepted" (Some code)
  | None => trace INFO "guardcert-phase/quotient-lowering/refused" None
  end.
Theorem traced_double_quotient_candidate_exact layouts cache flag quotient limit quotient_range live pool generated :
  traced_double_quotient_candidate layouts cache flag quotient limit quotient_range live pool generated =
  compile_double_quotient_candidate layouts cache flag quotient limit quotient_range live pool generated.
Proof.
  unfold traced_double_quotient_candidate,compile_double_quotient_candidate,double_phase_stage,trace.
  destruct (compile_double_tensor_loop layouts [quotient;cache]
    [quotient_range;DoubleNested.A.Interval 0 limit] (flag::live) pool (fst (fst generated))); reflexivity.
Qed.

Print Assumptions traced_double_quotient_prepared_loop_exact.
Print Assumptions traced_double_quotient_candidate_exact.
