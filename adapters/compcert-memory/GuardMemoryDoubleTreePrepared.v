From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import PolCertLoopGuard.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleTiledPrepared GuardMemoryDoubleReindexedTiling GuardMemoryDoubleRectangularPrepared
  GuardMemoryDoubleTreeCacheEnvironment GuardMemoryDoubleTreeCacheParameters.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module DBL := DoubleAssignmentIRs.Loop.
Module DoubleAssumption := PolCertLoopGuardFor DoubleAssignmentInstr DBL.

(** Unlike rectangular nonnegative caps, these intervals admit signed headers
    and the zero-initialized slots of source children that were never reached. *)
Definition double_tree_parameter_intervals (headers : list ident) (lower upper : ident -> Z) :=
  map (fun header=>(Z.min 0 (lower header),Z.max 0 (upper header))) headers.
Fixpoint double_tree_parameter_test slot (intervals : list (Z*Z)) := match intervals with
  | []=>DBL.LE (DBL.Constant 0) (DBL.Constant 0)
  | (lower,upper)::rest=>DBL.And
      (DBL.And (DBL.LE (DBL.Constant lower) (DBL.Var slot))
        (DBL.LE (DBL.Var slot) (DBL.Constant upper)))
      (double_tree_parameter_test (S slot) rest) end.
Theorem double_tree_parameter_test_true intervals : forall slot parameters,
  Forall2 (fun interval value=>fst interval<=value<=snd interval) intervals (skipn slot parameters) ->
  DBL.eval_test parameters (double_tree_parameter_test slot intervals)=true.
Proof.
  induction intervals as [|[lower upper] intervals IH]; intros slot parameters RANGES; [reflexivity|].
  inversion RANGES as [|interval value intervals' values RANGE REST EQINTERVAL EQVALUES]; subst interval intervals'.
  assert (HEAD : nth slot parameters 0=value) by (eapply double_rectangular_skip_head; symmetry; exact EQVALUES).
  assert (TAIL : skipn (S slot) parameters=values) by (eapply double_rectangular_skip_tail; symmetry; exact EQVALUES).
  cbn [double_tree_parameter_test DBL.eval_test DBL.eval_expr]; rewrite HEAD.
  apply andb_true_iff; split.
  - apply andb_true_iff; split; apply Z.leb_le; cbn in RANGE; lia.
  - apply IH; rewrite TAIL; exact REST.
Qed.
Theorem double_tree_cached_parameter_ranges headers cache lower upper temps :
  double_tree_cache_environment headers cache lower upper temps ->
  Forall2 (fun interval value=>fst interval<=value<=snd interval)
    (double_tree_parameter_intervals headers lower upper) (map (double_tree_cached_value cache temps) headers).
Proof.
  induction headers as [|header headers IH]; intro ENV; [constructor|].
  cbn [double_tree_parameter_intervals map]; constructor.
  - destruct (ENV header (or_introl eq_refl)) as [word [WORD RANGE]].
    unfold double_tree_cached_value; rewrite WORD; exact RANGE.
  - apply IH; intros key MEMBER; apply ENV; right; exact MEMBER.
Qed.
Definition double_tree_assumed_loop intervals body := DBL.Guard (double_tree_parameter_test 0 intervals) body.
Theorem double_tree_assumed_execution intervals parameters before after body :
  Forall2 (fun interval value=>fst interval<=value<=snd interval) intervals parameters ->
  (DBL.loop_semantics (double_tree_assumed_loop intervals body) parameters before after <->
   DBL.loop_semantics body parameters before after).
Proof.
  intro RANGES; unfold double_tree_assumed_loop.
  rewrite DoubleAssumption.guard_execution, (@double_tree_parameter_test_true intervals 0 parameters RANGES); reflexivity.
Qed.

(** The actual extraction, affine validation, tiled import and prepared codegen
    path proposes raw output. The final checker validates the adapted Loop that
    will actually be lowered, under the intervals established by capture. *)
Definition checked_double_tree_tiled_prepared_loop_progress phase
  (adapt : list (Z*Z) -> DBL.t -> result DBL.t) choices intervals (source : DBL.t) :=
  BIND proposed <- checked_double_tiled_prepared_loop phase source -;
  match proposed with
  | None=>pure None
  | Some (raw,witnesses)=>match adapt intervals raw with
    | Err _=>pure None
    | Okk candidate=>
      let '(_,context,vars) := source in
      BIND valid <- checked_double_reindexed_tiling_choices
        (double_tree_assumed_loop intervals (fst (fst source)),context,vars)
        (double_tree_assumed_loop intervals (fst (fst candidate)),context,vars) witnesses choices -;
      if valid then pure (Some candidate) else pure None
    end
  end.
Theorem checked_double_tree_tiled_prepared_loop_progress_at phase adapt choices intervals source generated
  parameters initial final :
  mayReturn (checked_double_tree_tiled_prepared_loop_progress phase adapt choices intervals source) (Some generated) ->
  length (snd (fst source))=length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  Forall2 (fun interval value=>fst interval<=value<=snd interval) intervals parameters ->
  DBL.loop_semantics (fst (fst source)) parameters initial final ->
  DBL.loop_semantics (fst (fst generated)) parameters initial final.
Proof.
  destruct source as [[body context] vars].
  intros RUN LENGTH NONALIAS RANGES SOURCE.
  unfold checked_double_tree_tiled_prepared_loop_progress in RUN.
  bind_imp_destruct RUN proposed PROPOSED.
  destruct proposed as [[raw witnesses]|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (adapt intervals raw) as [candidate|message]; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN valid VALID; destruct valid; [|apply mayReturn_pure in RUN; discriminate].
  apply mayReturn_pure in RUN; inversion RUN; subst candidate.
  destruct (@checked_double_reindexed_tiling_choices_sound
    (double_tree_assumed_loop intervals body,context,vars)
    (double_tree_assumed_loop intervals (fst (fst generated)),context,vars) witnesses choices VALID)
    as [swaps CHOSEN].
  pose proof (@validated_double_reindexed_tiling_loops_at
    (double_tree_assumed_loop intervals body)
    (double_tree_assumed_loop intervals (fst (fst generated))) context vars witnesses swaps
    (rev parameters) initial final ltac:(rewrite length_rev; symmetry; exact LENGTH) NONALIAS CHOSEN) as FORWARD.
  rewrite rev_involutive in FORWARD.
  apply (proj1 (@double_tree_assumed_execution intervals parameters initial final (fst (fst generated)) RANGES)).
  apply FORWARD; apply (proj2 (@double_tree_assumed_execution intervals parameters initial final body RANGES)); exact SOURCE.
Qed.

Print Assumptions double_tree_parameter_test_true.
Print Assumptions double_tree_cached_parameter_ranges.
Print Assumptions double_tree_assumed_execution.
Print Assumptions checked_double_tree_tiled_prepared_loop_progress_at.
