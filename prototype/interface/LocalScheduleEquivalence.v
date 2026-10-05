From Stdlib Require Import List.
From Guard Require Import AbstractSchedule.
Import ListNotations.
Set Implicit Arguments.

(** This adapter reuses the existing exchange-chain library. It adds the
    reverse execution direction needed by an equivalence contract. Neither
    instruction semantics nor an alias or overflow interpretation is fixed. *)
Section LOCAL_SCHEDULE.
Context {S Instruction : Type} (M : scheduling_model S Instruction).
Hypothesis INDEPENDENCE_SYMMETRIC :
  forall first second, independent M first second -> independent M second first.

Lemma schedule_certificate_reverse source target :
  schedule_certificate M source target -> schedule_certificate M target source.
Proof.
  intro CERT; induction CERT.
  - constructor.
  - constructor; assumption.
  - apply certificate_swap, INDEPENDENCE_SYMMETRIC; assumption.
  - eapply certificate_trans; [exact IHCERT2|exact IHCERT1].
Qed.

Context {O : Type} (observe : S -> O -> Prop).
Hypothesis OBSERVATION_TRANSPORT : forall first second,
  state_equivalent M first second -> forall observed,
    observe first observed <-> observe second observed.

Definition schedule_observes instructions entry observed :=
  exists final, schedule_run M instructions entry final /\ observe final observed.

Theorem certified_schedule_equivalent source target :
  schedule_certificate M source target -> forall entry observed,
  schedule_invariant M entry ->
  (schedule_observes target entry observed <-> schedule_observes source entry observed).
Proof.
  intros CERT entry observed INV; split; intros [final [RUN OBSERVE]].
  - destruct (certified_schedule_preserves (schedule_certificate_reverse CERT) INV RUN)
      as [original [SOURCE RELATED]].
    exists original; split; [exact SOURCE|].
    apply (proj1 (OBSERVATION_TRANSPORT final original RELATED observed)); exact OBSERVE.
  - destruct (certified_schedule_preserves CERT INV RUN) as [candidate [TARGET RELATED]].
    exists candidate; split; [exact TARGET|].
    apply (proj1 (OBSERVATION_TRANSPORT final candidate RELATED observed)); exact OBSERVE.
Qed.
End LOCAL_SCHEDULE.

Print Assumptions schedule_certificate_reverse.
Print Assumptions certified_schedule_equivalent.
