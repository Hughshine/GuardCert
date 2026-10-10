From Stdlib Require Import List String ZArith.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure Debugging.
From GuardMemory Require Import GuardMemoryDoublePolyhedral GuardMemoryDoubleTiledPrepared
  GuardMemoryDoubleReindexedTiling GuardMemoryDoubleTiledPhaseTrace
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleTreePrepared
  GuardMemoryDoubleTreeCandidate GuardMemoryDoubleTensorBackend GuardMemoryDoubleNestedBackend.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope string_scope.

(** Compilation diagnostics only. Each marker is the existing logical identity
    primitive; the exact-equality endpoints cover both acceptance and refusal. *)
Definition double_tree_boolean_trace (label : string) (decision : bool) :=
  double_phase_stage (label ++ if decision then "/accepted" else "/refused")
    (fun _ => decision).

Definition traced_double_tree_tiled_prepared_loop_progress phase
  (adapt : list (Z*Z) -> DoubleAssignmentIRs.Loop.t -> result DoubleAssignmentIRs.Loop.t)
  choices intervals (source : DoubleAssignmentIRs.Loop.t) :=
  BIND proposed <- double_phase_stage "tree/raw-pipeline"
    (fun _ => checked_double_tiled_prepared_loop phase source) -;
  match proposed with
  | None => pure None
  | Some (raw,witnesses) => match double_phase_stage "tree/adaptation" (fun _ => adapt intervals raw) with
    | Err _ => pure None
    | Okk candidate =>
      let '(_,context,vars) := source in
      BIND valid <- double_phase_stage "tree/final-generated-validation"
        (fun _ => checked_double_reindexed_tiling_choices
          (double_tree_assumed_loop intervals (fst (fst source)),context,vars)
          (double_tree_assumed_loop intervals (fst (fst candidate)),context,vars) witnesses choices) -;
      if double_tree_boolean_trace "tree/final-generated-validation" valid
      then pure (Some candidate) else pure None
    end
  end.

Theorem traced_double_tree_tiled_prepared_loop_progress_exact phase adapt choices intervals source :
  traced_double_tree_tiled_prepared_loop_progress phase adapt choices intervals source =
  checked_double_tree_tiled_prepared_loop_progress phase adapt choices intervals source.
Proof.
  unfold traced_double_tree_tiled_prepared_loop_progress,
    checked_double_tree_tiled_prepared_loop_progress, double_tree_boolean_trace,
    double_phase_stage, trace; reflexivity.
Qed.

Definition traced_compile_double_tree_candidate layouts tree cache flag lower upper live pool
  (generated : DoubleAssignmentIRs.Loop.t) :=
  let code := double_phase_stage "tree/machine-lowering" (fun _ =>
    compile_double_tensor_loop layouts (map cache (double_source_tree_parameters tree))
      (double_tree_candidate_intervals (double_source_tree_parameters tree) lower upper)
      (flag::live) pool (fst (fst generated))) in
  double_phase_stage (match code with
    | Some _ => "tree/machine-lowering/accepted"
    | None => "tree/machine-lowering/refused" end) (fun _ => code).

Theorem traced_compile_double_tree_candidate_exact layouts tree cache flag lower upper live pool generated :
  traced_compile_double_tree_candidate layouts tree cache flag lower upper live pool generated =
  compile_double_tree_candidate layouts tree cache flag lower upper live pool generated.
Proof.
  unfold traced_compile_double_tree_candidate, compile_double_tree_candidate,
    double_phase_stage, trace; reflexivity.
Qed.

Print Assumptions traced_double_tree_tiled_prepared_loop_progress_exact.
Print Assumptions traced_compile_double_tree_candidate_exact.
