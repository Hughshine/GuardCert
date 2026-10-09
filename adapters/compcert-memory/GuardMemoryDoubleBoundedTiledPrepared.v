From Stdlib Require Import List Bool ZArith Lia.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import PolCertLoopGuard.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleTiledPrepared GuardMemoryDoubleReindexedTiling.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module DBL := DoubleAssignmentIRs.Loop.
Module DoubleAssumption := PolCertLoopGuardFor DoubleAssignmentInstr DBL.

(** A model restriction consumed only under a proved captured-parameter range.
    It is not a new runtime check or an assertion supplied by a C source user. *)
Definition double_parameter_range_test limit :=
  DBL.And (DBL.LE (DBL.Constant 0) (DBL.Var 0))
    (DBL.LE (DBL.Var 0) (DBL.Constant limit)).
Definition double_bounded_assumed_loop limit body :=
  DBL.Guard (double_parameter_range_test limit) body.
Lemma double_parameter_range_test_true limit parameters :
  0 <= nth 0 parameters 0 <= limit ->
  DBL.eval_test parameters (double_parameter_range_test limit) = true.
Proof.
  intro RANGE; cbn [double_parameter_range_test DBL.eval_test DBL.eval_expr].
  apply andb_true_iff; split; apply Z.leb_le; lia.
Qed.
Lemma double_bounded_assumed_execution limit parameters before after body :
  0 <= nth 0 parameters 0 <= limit ->
  (DBL.loop_semantics (double_bounded_assumed_loop limit body) parameters before after <->
   DBL.loop_semantics body parameters before after).
Proof.
  intro RANGE; unfold double_bounded_assumed_loop.
  rewrite DoubleAssumption.guard_execution, (@double_parameter_range_test_true limit parameters RANGE).
  reflexivity.
Qed.

Definition checked_double_bounded_tiled_prepared_loop_progress phase
  (adapt : Z -> DBL.t -> result DBL.t) choices limit (source : DBL.t) :=
  BIND proposed <- checked_double_tiled_prepared_loop phase source -;
  match proposed with
  | None => pure None
  | Some (raw,witnesses) => match adapt limit raw with
    | Err _ => pure None
    | Okk candidate =>
      let '(_,context,vars) := source in
      BIND valid <- checked_double_reindexed_tiling_choices
        (double_bounded_assumed_loop limit (fst (fst source)),context,vars)
        (double_bounded_assumed_loop limit (fst (fst candidate)),context,vars) witnesses choices -;
      if valid then pure (Some candidate) else pure None
    end
  end.
Theorem checked_double_bounded_tiled_prepared_loop_progress_at phase adapt choices limit source generated parameters initial final :
  mayReturn (checked_double_bounded_tiled_prepared_loop_progress phase adapt choices limit source) (Some generated) ->
  length (snd (fst source))=length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  0 <= nth 0 parameters 0 <= limit ->
  DBL.loop_semantics (fst (fst source)) parameters initial final ->
  DBL.loop_semantics (fst (fst generated)) parameters initial final.
Proof.
  destruct source as [[body context] vars].
  intros RUN LENGTH NONALIAS RANGE SOURCE.
  unfold checked_double_bounded_tiled_prepared_loop_progress in RUN.
  bind_imp_destruct RUN proposed PROPOSED.
  destruct proposed as [[raw witnesses]|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (adapt limit raw) as [candidate|message]; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN valid VALID; destruct valid; [|apply mayReturn_pure in RUN; discriminate].
  apply mayReturn_pure in RUN; inversion RUN; subst candidate.
  destruct (@checked_double_reindexed_tiling_choices_sound
    (double_bounded_assumed_loop limit body,context,vars)
    (double_bounded_assumed_loop limit (fst (fst generated)),context,vars)
    witnesses choices VALID) as [swaps CHOSEN].
  pose proof (@validated_double_reindexed_tiling_loops_at
    (double_bounded_assumed_loop limit body)
    (double_bounded_assumed_loop limit (fst (fst generated))) context vars witnesses swaps
    (rev parameters) initial final ltac:(rewrite length_rev; symmetry; exact LENGTH)
    NONALIAS CHOSEN) as FORWARD.
  rewrite rev_involutive in FORWARD.
  apply (proj1 (@double_bounded_assumed_execution limit parameters initial final
    (fst (fst generated)) RANGE)).
  apply FORWARD.
  apply (proj2 (@double_bounded_assumed_execution limit parameters initial final body RANGE)); exact SOURCE.
Qed.

Print Assumptions double_bounded_assumed_execution.
Print Assumptions checked_double_bounded_tiled_prepared_loop_progress_at.
