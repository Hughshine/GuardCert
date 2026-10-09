From Stdlib Require Import List Bool ZArith Lia.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import PolCertLoopGuard.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleTiledPrepared GuardMemoryDoubleReindexedTiling GuardMemoryDoubleBoundedTiledPrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** All cap restrictions refer to the independently captured parameters.
    They constrain validation; emitted capture proves them before the candidate. *)
Fixpoint double_rectangular_parameter_test slot (caps : list Z) :=
  match caps with
  | []=>DBL.LE (DBL.Constant 0) (DBL.Constant 0)
  | cap::caps=>DBL.And
      (DBL.And (DBL.LE (DBL.Constant 0) (DBL.Var slot))
        (DBL.LE (DBL.Var slot) (DBL.Constant cap)))
      (double_rectangular_parameter_test (S slot) caps)
  end.
Lemma double_rectangular_skip_head slot : forall (parameters : list Z) value values,
  skipn slot parameters=value::values -> nth slot parameters 0=value.
Proof.
  induction slot as [|slot IH]; intros [|parameter parameters] value values CHECK;
    cbn [skipn nth] in *; try discriminate; [congruence|eapply IH; exact CHECK].
Qed.
Lemma double_rectangular_skip_tail slot : forall (parameters : list Z) value values,
  skipn slot parameters=value::values -> skipn (S slot) parameters=values.
Proof.
  induction slot as [|slot IH]; intros [|parameter parameters] value values CHECK;
    cbn [skipn] in *; try discriminate; [congruence|eapply IH; exact CHECK].
Qed.
Theorem double_rectangular_parameter_test_true caps : forall slot parameters,
  Forall2 (fun cap value => 0<=value<=cap) caps (skipn slot parameters) ->
  DBL.eval_test parameters (double_rectangular_parameter_test slot caps)=true.
Proof.
  induction caps as [|cap caps IH]; intros slot parameters RANGES; [reflexivity|].
  inversion RANGES as [|cap' value caps' values RANGE REST EQCAPS EQVALUES]; subst cap' caps'.
  assert (HEAD : nth slot parameters 0=value) by (eapply double_rectangular_skip_head; symmetry; exact EQVALUES).
  assert (TAIL : skipn (S slot) parameters=values) by (eapply double_rectangular_skip_tail; symmetry; exact EQVALUES).
  cbn [double_rectangular_parameter_test DBL.eval_test DBL.eval_expr]; rewrite HEAD.
  apply andb_true_iff; split.
  - apply andb_true_iff; split; apply Z.leb_le; lia.
  - apply IH; rewrite TAIL; exact REST.
Qed.
Definition double_rectangular_assumed_loop caps body := DBL.Guard (double_rectangular_parameter_test 0 caps) body.
Theorem double_rectangular_assumed_execution caps parameters before after body :
  Forall2 (fun cap value => 0<=value<=cap) caps parameters ->
  (DBL.loop_semantics (double_rectangular_assumed_loop caps body) parameters before after <->
   DBL.loop_semantics body parameters before after).
Proof.
  intro RANGES; unfold double_rectangular_assumed_loop.
  rewrite DoubleAssumption.guard_execution,
    (@double_rectangular_parameter_test_true caps 0 parameters RANGES); reflexivity.
Qed.

Definition checked_double_rectangular_tiled_prepared_loop_progress phase
  (adapt : list Z -> DBL.t -> result DBL.t) choices caps (source : DBL.t) :=
  BIND proposed <- checked_double_tiled_prepared_loop phase source -;
  match proposed with
  | None=>pure None
  | Some (raw,witnesses)=>match adapt caps raw with
    | Err _=>pure None
    | Okk candidate=>
      let '(_,context,vars) := source in
      BIND valid <- checked_double_reindexed_tiling_choices
        (double_rectangular_assumed_loop caps (fst (fst source)),context,vars)
        (double_rectangular_assumed_loop caps (fst (fst candidate)),context,vars) witnesses choices -;
      if valid then pure (Some candidate) else pure None
    end
  end.
Theorem checked_double_rectangular_tiled_prepared_loop_progress_at phase adapt choices caps source generated
  parameters initial final :
  mayReturn (checked_double_rectangular_tiled_prepared_loop_progress phase adapt choices caps source) (Some generated) ->
  length (snd (fst source))=length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  Forall2 (fun cap value => 0<=value<=cap) caps parameters ->
  DBL.loop_semantics (fst (fst source)) parameters initial final ->
  DBL.loop_semantics (fst (fst generated)) parameters initial final.
Proof.
  destruct source as [[body context] vars].
  intros RUN LENGTH NONALIAS RANGES SOURCE.
  unfold checked_double_rectangular_tiled_prepared_loop_progress in RUN.
  bind_imp_destruct RUN proposed PROPOSED.
  destruct proposed as [[raw witnesses]|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (adapt caps raw) as [candidate|message]; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN valid VALID; destruct valid; [|apply mayReturn_pure in RUN; discriminate].
  apply mayReturn_pure in RUN; inversion RUN; subst candidate.
  destruct (@checked_double_reindexed_tiling_choices_sound
    (double_rectangular_assumed_loop caps body,context,vars)
    (double_rectangular_assumed_loop caps (fst (fst generated)),context,vars)
    witnesses choices VALID) as [swaps CHOSEN].
  pose proof (@validated_double_reindexed_tiling_loops_at
    (double_rectangular_assumed_loop caps body)
    (double_rectangular_assumed_loop caps (fst (fst generated))) context vars witnesses swaps
    (rev parameters) initial final ltac:(rewrite length_rev; symmetry; exact LENGTH)
    NONALIAS CHOSEN) as FORWARD.
  rewrite rev_involutive in FORWARD.
  apply (proj1 (@double_rectangular_assumed_execution caps parameters initial final
    (fst (fst generated)) RANGES)); apply FORWARD.
  apply (proj2 (@double_rectangular_assumed_execution caps parameters initial final body RANGES)); exact SOURCE.
Qed.

Print Assumptions double_rectangular_parameter_test_true.
Print Assumptions double_rectangular_assumed_execution.
Print Assumptions checked_double_rectangular_tiled_prepared_loop_progress_at.
