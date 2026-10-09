From Stdlib Require Import List Bool ZArith Lia.
From polcert.polygen Require Import Result.
From polcert.src Require Import TilingWitness.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import PolCertParameterExtension PolCertQuotientParameter PolCertQuotientCapture.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleTiledPrepared GuardMemoryDoubleReindexedTiling GuardMemoryDoubleBoundedTiledPrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Module DoubleParameterExtension := PolCertParameterExtensionFor DoubleAssignmentInstr DBL.
Module DoubleQuotientModel := PolCertQuotientParameterFor DoubleAssignmentInstr DBL.
Module DoubleQuotientCapture := PolCertQuotientCaptureFor DoubleAssignmentInstr DBL.
Definition double_ceil_numerator divisor := DBL.Sum (DBL.Var 0) (DBL.Constant (divisor-1)).
Definition double_quotient_entry_test limit divisor :=
  DBL.And (DBL.LE (DBL.Constant 0) (DBL.Var 1))
    (DBL.And (DBL.LE (DBL.Var 1) (DBL.Constant limit))
      (DoubleQuotientModel.quotient_relation (double_ceil_numerator divisor) divisor)).
Definition double_quotient_assumed_loop limit divisor body :=
  DBL.Guard (double_quotient_entry_test limit divisor) body.
Lemma double_quotient_entry_true limit divisor parameters quotient :
  0<divisor -> 0<=nth 0 parameters 0<=limit ->
  quotient=DBL.eval_expr parameters (double_ceil_numerator divisor)/divisor ->
  DBL.eval_test (quotient::parameters) (double_quotient_entry_test limit divisor)=true.
Proof.
  intros POSITIVE RANGE VALUE.
  change ((0<=?nth 0 parameters 0) && ((nth 0 parameters 0<=?limit) &&
    DBL.eval_test (quotient::parameters)
      (DoubleQuotientModel.quotient_relation (double_ceil_numerator divisor) divisor))=true).
  repeat rewrite andb_true_iff; repeat split; try (apply Z.leb_le; lia).
  apply (proj2 (@DoubleQuotientModel.quotient_relation_exact (double_ceil_numerator divisor)
    divisor parameters quotient POSITIVE)); exact VALUE.
Qed.
Lemma double_quotient_assumed_execution limit divisor parameters quotient before after body :
  0<divisor -> 0<=nth 0 parameters 0<=limit ->
  quotient=DBL.eval_expr parameters (double_ceil_numerator divisor)/divisor ->
  (DBL.loop_semantics (double_quotient_assumed_loop limit divisor body) (quotient::parameters) before after <->
   DBL.loop_semantics body (quotient::parameters) before after).
Proof.
  intros POSITIVE RANGE VALUE; unfold double_quotient_assumed_loop.
  rewrite DoubleAssumption.guard_execution.
  rewrite (@double_quotient_entry_true limit divisor parameters quotient POSITIVE RANGE VALUE); reflexivity.
Qed.
Definition double_extend_parameter name (program : DBL.t) : DBL.t :=
  let '((body,context),vars) := program in
  (DoubleParameterExtension.lift_statement 0 body,context++[name],vars++[(name,tt)]).
Definition double_extend_tile_link link :=
  let expression := tl_expr link in
  {|tl_expr := {|ae_var_coeffs:=ae_var_coeffs expression;
                ae_param_coeffs:=ae_param_coeffs expression++[0]; ae_const:=ae_const expression|};
    tl_tile_size:=tl_tile_size link|}.
Definition double_extend_tiling_witness witness :=
  {|stw_point_dim:=stw_point_dim witness; stw_links:=map double_extend_tile_link (stw_links witness)|}.

(** Earlier scheduling/codegen still run on the original source. Final
    validation consumes the actual extended candidate and the proved quotient
    relation. Adaptation and witness extension are data, not semantic premises. *)
Definition checked_double_quotient_tiled_prepared_loop phase
  (adapt : Z -> Z -> DBL.t -> result DBL.t) choices limit divisor quotient_name (source : DBL.t) :=
  BIND proposed <- checked_double_tiled_prepared_loop phase source -;
  match proposed with
  | None => pure None
  | Some (raw,witnesses) => match adapt limit divisor (double_extend_parameter quotient_name raw) with
    | Err _ => pure None
    | Okk candidate =>
      let '((body,context),vars) := double_extend_parameter quotient_name source in
      let target := fst (fst candidate) in
      BIND valid <- checked_double_reindexed_tiling_choices
        (double_quotient_assumed_loop limit divisor body,context,vars)
        (double_quotient_assumed_loop limit divisor target,context,vars)
        (map double_extend_tiling_witness witnesses) choices -;
      if valid then pure (Some (target,context,vars)) else pure None end
  end.
Theorem checked_double_quotient_tiled_prepared_loop_at phase adapt choices limit divisor quotient_name
  source generated parameters quotient initial final :
  mayReturn (checked_double_quotient_tiled_prepared_loop phase adapt choices limit divisor quotient_name source)
    (Some generated) ->
  length (snd (fst source))=length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  0<divisor -> 0<=nth 0 parameters 0<=limit ->
  quotient=DBL.eval_expr parameters (double_ceil_numerator divisor)/divisor ->
  DBL.loop_semantics (fst (fst source)) parameters initial final ->
  DBL.loop_semantics (fst (fst generated)) (quotient::parameters) initial final.
Proof.
  destruct source as [[body context] vars].
  intros RUN LENGTH NONALIAS POSITIVE RANGE VALUE SOURCE.
  unfold checked_double_quotient_tiled_prepared_loop in RUN.
  bind_imp_destruct RUN proposed PROPOSED.
  destruct proposed as [[raw witnesses]|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (adapt limit divisor (double_extend_parameter quotient_name raw)) as [[[target ignored_context] ignored_vars]|error];
    [|apply mayReturn_pure in RUN; discriminate].
  cbn [double_extend_parameter] in RUN.
  bind_imp_destruct RUN valid VALID; destruct valid; [|apply mayReturn_pure in RUN; discriminate].
  apply mayReturn_pure in RUN; inversion RUN; subst generated.
  destruct (@checked_double_reindexed_tiling_choices_sound
    (double_quotient_assumed_loop limit divisor (DoubleParameterExtension.lift_statement 0 body),context++[quotient_name],vars++[(quotient_name,tt)])
    (double_quotient_assumed_loop limit divisor target,context++[quotient_name],vars++[(quotient_name,tt)])
    (map double_extend_tiling_witness witnesses) choices VALID) as [swaps CHOSEN].
  pose proof (@validated_double_reindexed_tiling_loops_at
    (double_quotient_assumed_loop limit divisor (DoubleParameterExtension.lift_statement 0 body))
    (double_quotient_assumed_loop limit divisor target)
    (context++[quotient_name]) (vars++[(quotient_name,tt)]) (map double_extend_tiling_witness witnesses)
    swaps (rev (quotient::parameters)) initial final
    ltac:(rewrite length_rev,length_app; cbn in LENGTH |- *; lia) NONALIAS CHOSEN) as FORWARD.
  rewrite rev_involutive in FORWARD.
  apply (proj1 (@double_quotient_assumed_execution limit divisor parameters quotient initial final target POSITIVE RANGE VALUE)).
  apply FORWARD.
  apply (proj2 (@double_quotient_assumed_execution limit divisor parameters quotient initial final
    (DoubleParameterExtension.lift_statement 0 body) POSITIVE RANGE VALUE)).
  apply (proj2 (@DoubleParameterExtension.parameter_extension_exact body parameters quotient initial final)); exact SOURCE.
Qed.

Print Assumptions DoubleParameterExtension.parameter_extension_exact.
Print Assumptions DoubleQuotientModel.quotient_relation_exact.
Print Assumptions DoubleQuotientCapture.quotient_capture_execution.
Print Assumptions DoubleQuotientCapture.quotient_capture_writes.
Print Assumptions double_quotient_assumed_execution.
Print Assumptions checked_double_quotient_tiled_prepared_loop_at.
