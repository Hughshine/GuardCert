From Stdlib Require Import List Bool ZArith.
From polcert.src Require Import OpenScop TilingWitness.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleUniformPrepared GuardMemoryDoubleExtractedTiling
  GuardMemoryDoubleTiledPrepared GuardMemoryDoubleReindexedTiling.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition checked_double_reindexed_tiled_prepared_loop_progress phase
  (adapt : Z -> DoubleAssignmentIRs.Loop.t -> result DoubleAssignmentIRs.Loop.t)
  choices limit (source : DoubleAssignmentIRs.Loop.t) :=
  BIND proposed <- checked_double_tiled_prepared_loop phase source -;
  match proposed with
  | None => pure None
  | Some (raw,witnesses) => match adapt limit raw with
    | Err _ => pure None
    | Okk candidate =>
      let '(_,context,vars) := source in
      BIND valid <- checked_double_reindexed_tiling_choices source
        (fst (fst candidate),context,vars) witnesses choices -;
      if valid then pure (Some candidate) else pure None
    end
  end.
Theorem checked_double_reindexed_tiled_prepared_loop_progress_at phase adapt choices limit source generated parameters initial final :
  mayReturn (checked_double_reindexed_tiled_prepared_loop_progress phase adapt choices limit source) (Some generated) ->
  length (snd (fst source))=length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst source)) parameters initial final ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) parameters initial final.
Proof.
  destruct source as [[body context] vars].
  intros RUN LENGTH NONALIAS SOURCE; unfold checked_double_reindexed_tiled_prepared_loop_progress in RUN.
  bind_imp_destruct RUN proposed PROPOSED.
  destruct proposed as [[raw witnesses]|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (adapt limit raw) as [candidate|message]; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN valid VALID; destruct valid; [|apply mayReturn_pure in RUN; discriminate].
  apply mayReturn_pure in RUN; inversion RUN; subst candidate.
  destruct (@checked_double_reindexed_tiling_choices_sound (body,context,vars)
    (fst (fst generated),context,vars) witnesses choices VALID) as [swaps CHOSEN].
  pose proof (@validated_double_reindexed_tiling_loops_at body (fst (fst generated)) context vars witnesses swaps
    (rev parameters) initial final ltac:(rewrite length_rev; symmetry; exact LENGTH) NONALIAS CHOSEN) as FORWARD.
  rewrite rev_involutive in FORWARD; apply FORWARD; exact SOURCE.
Qed.

Print Assumptions checked_double_reindexed_tiled_prepared_loop_progress_at.
