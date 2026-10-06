From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightRegionProgress.
From GuardInterface Require Import GuardInterface ClightMaterializedCheck
  ClightPrivateScan ClightPrivateScanHost ClightPrivateScanSafety ClightQuietDeterminacy.
Set Implicit Arguments.

(** A finite source execution is a domain receipt, not an assumption that the
    optimization premise holds. Quiet sources do not depend on call semantics. *)
Definition materialized_source_completion source entry :=
  exists fe after final,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry)
      (entry_memory entry) source E0 after final Out_normal.

Lemma materialized_source_receipt fe source entry :
  quiet_statement source=true -> materialized_source_completion source entry ->
  exists after final,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry)
      (entry_memory entry) source E0 after final Out_normal.
Proof.
  intros QUIET [other [after [final RUN]]]; exists after,final.
  eapply quiet_execution_preserved; [split; reflexivity|exact RUN|exact QUIET].
Qed.

(** A domain library supplies one actual execution and its entry frame.
    The language library discharges primitive safety, defined dispatch, and
    soundness of every completed execution using quiet determinacy. *)
Definition materialized_execution_certificate
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  {O : Type} (observe : fragment_observation -> O -> Prop) ports
  (domain premise : clight_entry -> Prop) (test : materialized_check)
  (ENCODE : forall entry, domain entry -> exists accepted after,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry)
      (entry_memory entry) (materialized_body test) E0 after (entry_memory entry) Out_normal /\
    expression_test (materialized_condition test)
      (Entry (entry_ge entry) (entry_env entry) after (entry_memory entry)) accepted /\
    temp_agree ports (entry_temps entry) after /\ (accepted=true -> premise entry)) :
  guard_certificate (materialized_host fe observe) domain premise
    (private_scan_entry_frame ports) (private_scan_entry_frame ports) test.
Proof.
  constructor.
  - intros entry DOMAIN; destruct (ENCODE entry DOMAIN) as [accepted [after [RUN [TEST _]]]].
    eapply materialized_execution_safe; eassumption.
  - intros entry DOMAIN; destruct (ENCODE entry DOMAIN) as [accepted [after [RUN [TEST _]]]].
    exists accepted,(Entry (entry_ge entry) (entry_env entry) after (entry_memory entry)).
    exists after; auto.
  - intros entry accepted checked DOMAIN [other [OTHER [OTHER_TEST SAME]]]; subst checked.
    destruct (ENCODE entry DOMAIN) as [answer [after [RUN [TEST [FRAME PREMISE]]]]].
    destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN
      (private_scan_quiet (materialized_supported test)) _ _ _ _ OTHER)
      as [_ [TEMPS _]]; subst other.
    assert (ANSWER : answer=accepted) by (eapply scan_expression_test_unique; eassumption).
    subst answer; destruct accepted; cbn.
    + split; [apply PREMISE; reflexivity|repeat split; try reflexivity; exact FRAME].
    + repeat split; try reflexivity; exact FRAME.
Defined.

Print Assumptions materialized_source_receipt.
Print Assumptions materialized_execution_certificate.
