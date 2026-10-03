From Stdlib Require Import Bool.
From Guard Require Import StatefulGuard.
Set Implicit Arguments.

Record stateful_test_sequence {S} (language : stateful_language S) := StatefulTestSequence {
  stateful_sequence : stateful_test language -> stateful_test language -> stateful_test language;
  stateful_sequence_intro : forall first second state middle final accepted rest,
    stateful_test_run language first state accepted middle ->
    (accepted = true -> stateful_test_run language second middle rest final) ->
    stateful_test_run language (stateful_sequence first second) state (accepted && rest)
      (if accepted then final else middle)
}.

(** Short-circuit composition preserves the first property through the second
    check. Domain stability and frame composition are explicit obligations. *)
Definition projected_guard_conjunction S (language : stateful_language S)
  (sequence : stateful_test_sequence language) domain first_property second_property frame
  (first : projected_guard_encoding language domain first_property frame)
  (second : projected_guard_encoding language domain second_property frame)
  (DOMAIN_FRAME : forall state after, domain state -> frame state after -> domain after)
  (FRAME_TRANS : forall first middle last, frame first middle -> frame middle last -> frame first last)
  (FIRST_FRAME : forall state after, first_property state -> frame state after -> first_property after) :
  projected_guard_encoding language domain
    (fun state => first_property state /\ second_property state) frame.
Proof.
  refine (@ProjectedGuardEncoding S language domain
    (fun state => first_property state /\ second_property state) frame
    (stateful_sequence sequence (projected_guard_test first) (projected_guard_test second)) _).
  intros state DOMAIN.
  destruct (@projected_guard_execution S language domain first_property frame first state DOMAIN)
    as [accepted [middle [FIRST [FIRST_AGREE FIRST_PROPERTY]]]].
  destruct accepted.
  - destruct (@projected_guard_execution S language domain second_property frame second middle
      (DOMAIN_FRAME state middle DOMAIN FIRST_AGREE))
      as [rest [last [SECOND [SECOND_AGREE SECOND_PROPERTY]]]].
    exists rest,last; split.
    + change rest with (true && rest).
      eapply (@stateful_sequence_intro S language sequence (projected_guard_test first) (projected_guard_test second)
        state middle last true rest); [exact FIRST|intro; exact SECOND].
    + split; [eapply FRAME_TRANS; eassumption|].
      intro ACCEPT; split.
      * eapply FIRST_FRAME; [apply FIRST_PROPERTY; reflexivity|exact SECOND_AGREE].
      * apply SECOND_PROPERTY; exact ACCEPT.
  - exists false,middle; split.
    + change false with (false && false).
      eapply (@stateful_sequence_intro S language sequence (projected_guard_test first) (projected_guard_test second)
        state middle middle false false); [exact FIRST|discriminate].
    + split; [exact FIRST_AGREE|discriminate].
Defined.
Print Assumptions projected_guard_conjunction.
