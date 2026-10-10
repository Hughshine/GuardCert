From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import PolCertLoopGuard.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleTiledPrepared GuardMemoryDoubleReindexedTiling GuardMemoryDoubleRectangularPrepared
  GuardMemoryDoubleTreeCacheEnvironment GuardMemoryDoubleTreeCacheParameters
  GuardMemoryDoubleTreePrepared GuardMemoryDoubleShiftedTiling GuardMemoryDoubleCommonPrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.
(** The actual extraction, affine validation, tiled import and prepared codegen
    path proposes raw output. The final checker validates the adapted Loop that
    will actually be lowered, under the intervals established by capture. *)
Definition checked_double_tree_source_prepared_loop_progress phase
  (adapt : list (Z*Z) -> DBL.t -> DBL.t -> result DBL.t) (shifts_proposal : DBL.t -> list Z) choices intervals (source : DBL.t) :=
  BIND proposed <- checked_double_common_prepared_loop phase source -;
  match proposed with
  | None=>pure None
  | Some (raw,witnesses)=>match adapt intervals source raw with
    | Err _=>pure None
    | Okk candidate=>
      let '(_,context,vars) := source in
      BIND valid <- checked_double_shifted_tiling_choices
        (double_tree_assumed_loop intervals (fst (fst source)),context,vars)
        (double_tree_assumed_loop intervals (fst (fst candidate)),context,vars) witnesses (map (fun swaps => (swaps,shifts_proposal candidate)) choices) -;
      if valid then pure (Some candidate) else pure None
    end
  end.
Theorem checked_double_tree_source_prepared_loop_progress_at phase adapt shifts_proposal choices intervals source generated
  parameters initial final :
  mayReturn (checked_double_tree_source_prepared_loop_progress phase adapt shifts_proposal choices intervals source) (Some generated) ->
  length (snd (fst source))=length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  Forall2 (fun interval value=>fst interval<=value<=snd interval) intervals parameters ->
  DBL.loop_semantics (fst (fst source)) parameters initial final ->
  DBL.loop_semantics (fst (fst generated)) parameters initial final.
Proof.
  destruct source as [[body context] vars].
  intros RUN LENGTH NONALIAS RANGES SOURCE.
  unfold checked_double_tree_source_prepared_loop_progress in RUN.
  bind_imp_destruct RUN proposed PROPOSED.
  destruct proposed as [[raw witnesses]|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (adapt intervals ((body,context),vars) raw) as [candidate|message]; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN valid VALID; destruct valid; [|apply mayReturn_pure in RUN; discriminate].
  apply mayReturn_pure in RUN; inversion RUN; subst candidate.
  destruct (@checked_double_shifted_tiling_choices_sound
    (double_tree_assumed_loop intervals body,context,vars)
    (double_tree_assumed_loop intervals (fst (fst generated)),context,vars) witnesses (map (fun swaps => (swaps,shifts_proposal generated)) choices) VALID)
    as [swaps [shifts CHOSEN]].
  pose proof (@validated_double_shifted_tiling_loops_at
    (double_tree_assumed_loop intervals body)
    (double_tree_assumed_loop intervals (fst (fst generated))) context vars witnesses swaps shifts
    (rev parameters) initial final ltac:(rewrite length_rev; symmetry; exact LENGTH) NONALIAS CHOSEN) as FORWARD.
  rewrite rev_involutive in FORWARD.
  apply (proj1 (@double_tree_assumed_execution intervals parameters initial final (fst (fst generated)) RANGES)).
  apply FORWARD; apply (proj2 (@double_tree_assumed_execution intervals parameters initial final body RANGES)); exact SOURCE.
Qed.

Print Assumptions checked_double_tree_source_prepared_loop_progress_at.
