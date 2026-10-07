From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition.
From GuardInterface Require Import GuardInterface ClightMaterializedCheck ClightPrivateScan ClightPrivateScanSafety ClightQuietDeterminacy.
Set Implicit Arguments.

(** Unlike the simple frame adapter, this producer retains a relation to
    private values established by the check, such as a captured load. *)
Definition materialized_entry_execution_certificate
  (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  {O : Type} (observe : fragment_observation -> O -> Prop)
  (domain premise : clight_entry -> Prop) (accepted_entry refused_entry : clight_entry -> clight_entry -> Prop)
  (test : materialized_check)
  (ENCODE : forall entry, domain entry -> exists accepted after,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry)
      (entry_memory entry) (materialized_body test) E0 after (entry_memory entry) Out_normal /\
    expression_test (materialized_condition test)
      (Entry (entry_ge entry) (entry_env entry) after (entry_memory entry)) accepted /\
    (if accepted then premise entry /\ accepted_entry entry
      (Entry (entry_ge entry) (entry_env entry) after (entry_memory entry))
     else refused_entry entry (Entry (entry_ge entry) (entry_env entry) after (entry_memory entry)))) :
  guard_certificate (materialized_host fe observe) domain premise accepted_entry refused_entry test.
Proof.
  constructor.
  - intros entry DOMAIN; destruct (ENCODE entry DOMAIN) as [accepted [after [RUN [TEST _]]]].
    eapply materialized_execution_safe; eassumption.
  - intros entry DOMAIN; destruct (ENCODE entry DOMAIN) as [accepted [after [RUN [TEST _]]]].
    exists accepted,(Entry (entry_ge entry) (entry_env entry) after (entry_memory entry)).
    exists after; auto.
  - intros entry accepted checked DOMAIN [other [OTHER [OTHER_TEST SAME]]]; subst checked.
    destruct (ENCODE entry DOMAIN) as [answer [after [RUN [TEST SOUND]]]].
    destruct (@quiet_execution_determinate _ _ _ _ _ _ _ _ _ _ RUN
      (private_scan_quiet (materialized_supported test)) _ _ _ _ OTHER)
      as [_ [TEMPS _]]; subst other.
    assert (ANSWER : answer=accepted) by (eapply scan_expression_test_unique; eassumption).
    subst answer; exact SOUND.
Defined.

Print Assumptions materialized_entry_execution_certificate.
