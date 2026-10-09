From Stdlib Require Import List Bool ZArith.
From polcert.src Require Import Base OpenScop.
From polcert.polygen Require Import Result.
From polcert.lib Require Import ImpureAlarmConfig Misc.
From Vpl Require Import Impure.
From Guard Require Import PolCertPreparedParameters.
From GuardMemory Require Import GuardMemoryDoubleAssignment
  GuardMemoryDoublePolyhedral GuardMemoryDoublePrepared.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Module DoubleAssignmentParameters := PolCertPreparedParameters DoubleAssignmentIRs.
Module AtPoly := DoubleAssignmentIRs.PolyLang.
Module AtLoop := DoubleAssignmentIRs.Loop.

(** Validation and generation preserve named parameter context. The fixed
    environment below is supplied by the actual runtime capture, rather than
    extracted from a wrapped execution's existential environment. *)
Lemma validated_double_parameter_context source candidate :
  mayReturn (DoubleAssignmentValidator.validate source candidate) true ->
  snd (fst source) = snd (fst candidate).
Proof.
  destruct source as [[sp sc] sv], candidate as [[cp cc] cv].
  intro VALID; unfold DoubleAssignmentValidator.validate in VALID.
  bind_imp_destruct VALID wf1 WF1; bind_imp_destruct VALID wf2 WF2.
  bind_imp_destruct VALID eqdom EQDOM; bind_imp_destruct VALID checks CHECKS.
  apply mayReturn_pure in VALID.
  assert (EQ : eqdom = true) by (repeat rewrite andb_true_iff in VALID; tauto).
  pose proof (DoubleAssignmentValidator.check_eqdom_pprog_correct
    (sp,sc,sv) (cp,cc,cv) eqdom EQDOM EQ) as SAME.
  destruct (SAME sp cp sc cc sv cv eq_refl eq_refl) as [CONTEXT _].
  exact CONTEXT.
Qed.

Theorem checked_double_schedule_codegen_correct_at source candidate generated parameters initial final :
  mayReturn (checked_double_schedule_codegen source candidate) (Some generated) ->
  length (snd (fst source)) = length parameters ->
  DoubleAssignmentInstr.NonAlias initial ->
  AtLoop.loop_semantics (fst (fst generated)) parameters initial final ->
  AtPoly.poly_instance_list_semantics (rev parameters) source initial final.
Proof.
  intros CHECK LENGTH NONALIAS EXEC.
  unfold checked_double_schedule_codegen in CHECK.
  bind_imp_destruct CHECK valid VALID; destruct valid;
    [|apply mayReturn_pure in CHECK; discriminate].
  bind_imp_destruct CHECK actual GENERATED.
  apply mayReturn_pure in CHECK; inversion CHECK; subst actual.
  pose proof (@validated_double_parameter_context source candidate VALID) as CONTEXT.
  destruct (DoubleAssignmentValidator.validate_preserve_wf_pprog _ _ _ VALID eq_refl) as [_ WF].
  assert (CLENGTH : length (snd (fst candidate)) = length parameters) by (rewrite <- CONTEXT; exact LENGTH).
  pose proof (@DoubleAssignmentParameters.prepared_codegen_correct_at
    candidate parameters initial final generated GENERATED WF CLENGTH EXEC) as MODEL.
  destruct source as [[sp sc] sv], candidate as [[cp cc] cv].
  destruct (@DoubleAssignmentValidator.validate_correct'
    (sp,sc,sv) (cp,cc,cv) sc cc sp cp sv cv (rev parameters)
    initial final true VALID eq_refl eq_refl eq_refl)
    as [result [SOURCE SAME]].
  - rewrite rev_length. exact LENGTH.
  - exact NONALIAS.
  - exact MODEL.
  - unfold DoubleAssignmentIRs.State.eq, DoubleAssignmentInstr.State.eq in SAME.
    subst result; exact SOURCE.
Qed.

Theorem checked_double_prepared_phase_correct_at schedule source generated parameters initial final :
  mayReturn (checked_double_prepared_phase schedule source) (Some generated) ->
  length (snd (fst source)) = length parameters ->
  DoubleAssignmentInstr.NonAlias initial ->
  AtLoop.loop_semantics (fst (fst generated)) parameters initial final ->
  AtPoly.poly_instance_list_semantics (rev parameters) source initial final.
Proof.
  unfold checked_double_prepared_phase.
  destruct (export_double_model source) as [before|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (schedule before) as [after|message];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (DP.from_openscop_like_source source after) as [proposed|message];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  apply checked_double_schedule_codegen_correct_at.
Qed.

Theorem checked_double_prepared_loop_correct_at schedule source generated parameters initial final :
  mayReturn (checked_double_prepared_loop schedule source) (Some generated) ->
  length (snd (fst source)) = length parameters ->
  DoubleAssignmentInstr.NonAlias initial ->
  AtLoop.loop_semantics (fst (fst generated)) parameters initial final ->
  AtLoop.loop_semantics (fst (fst source)) parameters initial final.
Proof.
  unfold checked_double_prepared_loop.
  destruct (DoubleAssignmentExtractor.extractor source) as [model|message] eqn:EXTRACT;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intros RUN LENGTH NONALIAS EXEC.
  assert (MLENGTH : length (snd (fst model)) = length parameters).
  { destruct source as [[body context] variables].
    destruct (DoubleAssignmentExtractor.extractor_success_inv _ _ _ _ EXTRACT)
      as [pis [_ [_ SAME]]]; rewrite SAME; exact LENGTH. }
  pose proof (@checked_double_prepared_phase_correct_at schedule model generated
    parameters initial final RUN MLENGTH NONALIAS EXEC) as MODEL.
  destruct (@DoubleAssignmentParameters.extractor_correct_at
    source model parameters initial final EXTRACT LENGTH MODEL) as [result [SOURCE SAME]].
  unfold DoubleAssignmentIRs.State.eq, DoubleAssignmentInstr.State.eq in SAME.
  subst result; exact SOURCE.
Qed.

Print Assumptions DoubleAssignmentParameters.prepare_codegen_semantics_correct_at.
Print Assumptions DoubleAssignmentParameters.prepared_codegen_raw_correct_at.
Print Assumptions DoubleAssignmentParameters.prepared_codegen_correct_at.
Print Assumptions DoubleAssignmentParameters.extractor_correct_at.
Print Assumptions validated_double_parameter_context.
Print Assumptions checked_double_schedule_codegen_correct_at.
Print Assumptions checked_double_prepared_phase_correct_at.
Print Assumptions checked_double_prepared_loop_correct_at.
