From Stdlib Require Import List.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.

(** The choice kernel knows only a checker and its contract. *)
Fixpoint first_checked_candidate {Proposal Candidate}
  (check:Proposal->CoreAlarmed.Base.imp(option Candidate))(proposals:list Proposal) :=
  match proposals with
  | []=>pure None
  | proposal::rest=>BIND result <- check proposal -;
      match result with Some candidate=>pure(Some candidate)|None=>first_checked_candidate check rest end end.
Theorem first_checked_candidate_sound {Proposal Candidate}
  (contract:Candidate->Prop)(check:Proposal->CoreAlarmed.Base.imp(option Candidate)) proposals candidate :
  (forall proposal target, mayReturn(check proposal)(Some target)->contract target) ->
  mayReturn(first_checked_candidate check proposals)(Some candidate)->contract candidate.
Proof.
  intro SOUND; induction proposals; intro CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; discriminate.
  - bind_imp_destruct CHECK selected SELECTED; destruct selected as [target|].
    + apply mayReturn_pure in CHECK; inversion CHECK; subst; eapply SOUND; exact SELECTED.
    + apply IHproposals; exact CHECK.
Qed.
Print Assumptions first_checked_candidate_sound.
