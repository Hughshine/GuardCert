From Stdlib Require Import Bool.
Set Implicit Arguments.

(** The instance chooses states, observations, and the meaning of execution.
    Checks can update state. The conditional constructor executes its selected
    command at the state produced by the check. *)
Record stateful_language (S : Type) := StatefulLanguage {
  stateful_command : Type;
  stateful_test : Type;
  stateful_observation : Type;
  stateful_command_run : stateful_command -> S -> stateful_observation -> Prop;
  stateful_test_run : stateful_test -> S -> bool -> S -> Prop;
  stateful_conditional : stateful_test -> stateful_command -> stateful_command -> stateful_command;
  stateful_conditional_intro : forall test yes no state observed,
    forall accepted checked, stateful_test_run test state accepted checked ->
      stateful_command_run (if accepted then yes else no) checked observed ->
      stateful_command_run (stateful_conditional test yes no) state observed
}.
Arguments stateful_command_run {S} _ _ _ _.
Arguments stateful_test_run {S} _ _ _ _ _.
Arguments stateful_conditional {S} _ _ _ _.

(** The encoder proves execution on the source-derived domain, preservation of
    an instance-defined frame, and the presumption at the checked state.
    Refusal is conservative: it carries no proof of the negated presumption. *)
Record projected_guard_encoding {S} (language : stateful_language S)
  (domain presumption : S -> Prop) (frame : S -> S -> Prop) := ProjectedGuardEncoding {
  projected_guard_test : stateful_test language;
  projected_guard_execution : forall state, domain state ->
    exists accepted checked, stateful_test_run language projected_guard_test state accepted checked /\
      frame state checked /\ (accepted = true -> presumption checked)
}.

(** Source execution supplies the check domain. The instance transports source
    observations across the frame and proves the candidate under the presumption. *)
Theorem stateful_guard_preservation S (language : stateful_language S)
  domain presumption frame source candidate
  (encoding : projected_guard_encoding language domain presumption frame) :
  (forall state observed, stateful_command_run language source state observed -> domain state) ->
  (forall state checked observed, frame state checked ->
    stateful_command_run language source state observed -> stateful_command_run language source checked observed) ->
  (forall checked observed, presumption checked ->
    stateful_command_run language source checked observed -> stateful_command_run language candidate checked observed) ->
  forall state observed, stateful_command_run language source state observed ->
    stateful_command_run language
      (stateful_conditional language (projected_guard_test encoding) candidate source) state observed.
Proof.
  intros DOMAIN TRANSPORT LOCAL state observed SOURCE.
  destruct (@projected_guard_execution S language domain presumption frame encoding state (DOMAIN state observed SOURCE))
    as [accepted [checked [CHECK [FRAME PROPERTY]]]].
  eapply stateful_conditional_intro; [exact CHECK|].
  pose proof (TRANSPORT state checked observed FRAME SOURCE) as PRESERVED.
  destruct accepted; [apply LOCAL; [apply PROPERTY; reflexivity|exact PRESERVED]|exact PRESERVED].
Qed.
Print Assumptions stateful_guard_preservation.
