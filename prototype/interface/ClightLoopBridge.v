From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightRegionProgress.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  DeterministicLocalReasoning ClightQuietDeterminacy.
Set Implicit Arguments.

(** This is a ghost completion witness. The runtime guard cannot query it.
    Source progress/placement must establish its use for a terminating region. *)
Definition quiet_source_completion source entry := exists observed,
  forall fe, clight_fragment_run fe source entry observed.

Theorem quiet_source_completion_from_run source fe entry observed :
  quiet_statement source = true -> clight_fragment_run fe source entry observed ->
  quiet_source_completion source entry.
Proof.
  intros QUIET RUN; exists observed; intro other_fe.
  eapply (@quiet_execution_preserved fe other_fe (entry_ge entry) (entry_ge entry));
    [split; [reflexivity|intros; reflexivity]|exact RUN|exact QUIET].
Qed.

(** The observer may hide private temporaries or relate memory
    representations. Determinacy applies to raw Clight results, not to the
    possibly non-unique set of saturated public observations. *)
Theorem quiet_observed_forward_loop_equivalent fe
  (observe : fragment_observation -> fragment_observation -> Prop) domain premise source candidate
  (SYMMETRIC : forall first second, observe first second -> observe second first)
  (TRANSITIVE : forall first middle last, observe first middle -> observe middle last -> observe first last)
  (COMPLETE : forall entry, domain entry -> premise entry -> quiet_source_completion source entry)
  (CANDIDATE_QUIET : quiet_statement candidate = true)
  (FORWARD : forall entry original, domain entry -> premise entry ->
    clight_fragment_run fe source entry original ->
    exists transformed, clight_fragment_run fe candidate entry transformed /\ observe original transformed) :
  conditional_equivalence (readonly_clight_host fe observe) domain premise source candidate.
Proof.
  apply saturated_forward_bridge_equivalent with
    (raw_runs := clight_fragment_run fe) (observe := observe).
  - intros; reflexivity.
  - intros; reflexivity.
  - intros entry DOMAIN PREMISE; destruct (COMPLETE entry DOMAIN PREMISE) as [original RUN].
    exists original; apply RUN.
  - intros entry original DOMAIN PREMISE SOURCE.
    destruct (FORWARD entry original DOMAIN PREMISE SOURCE) as [transformed [TARGET EQUIVALENT]].
    exists transformed; split; [exact TARGET|].
    intro observed; split; intro VISIBLE; eapply TRANSITIVE;
      [apply SYMMETRIC; exact EQUIVALENT|exact VISIBLE|exact EQUIVALENT|exact VISIBLE].
  - intros entry first second _ _ FIRST SECOND; eapply quiet_fragment_determinate; eassumption.
Qed.

(** Users may reuse an existing forward loop execution theorem. Completion
    and the actual quiet-candidate syntax discharge the missing direction.
    All raw exits are preserved, rather than only a detached memory schedule. *)
Theorem quiet_forward_loop_equivalent fe domain premise source candidate
  (COMPLETE : forall entry, domain entry -> premise entry -> quiet_source_completion source entry)
  (CANDIDATE_QUIET : quiet_statement candidate = true)
  (FORWARD : forall entry observed, domain entry -> premise entry ->
    clight_fragment_run fe source entry observed -> clight_fragment_run fe candidate entry observed) :
  conditional_equivalence (readonly_clight_host fe (@eq fragment_observation)) domain premise source candidate.
Proof.
  apply forward_bridge_equivalent.
  - intros entry DOMAIN PREMISE; destruct (COMPLETE entry DOMAIN PREMISE) as [observed RUN].
    exists observed, observed; split; [apply RUN|reflexivity].
  - intros entry observed DOMAIN PREMISE [raw [RUN SAME]]; subst raw.
    exists observed; split; [apply FORWARD; assumption|reflexivity].
  - intros entry first second _ _ FIRST SECOND; eapply quiet_exact_host_determinate; eassumption.
Qed.

Print Assumptions quiet_source_completion_from_run.
Print Assumptions quiet_forward_loop_equivalent.
Print Assumptions quiet_observed_forward_loop_equivalent.
