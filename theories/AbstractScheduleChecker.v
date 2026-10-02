From Stdlib Require Import List Bool Sorting.Permutation.
From Guard Require Import AbstractSchedule.
Import ListNotations.
Set Implicit Arguments.

Section CHECKER.
Context {S Instruction} (M : scheduling_model S Instruction).
Variable instruction_eq : forall a b : Instruction, {a = b} + {a <> b}.
Variable independentb : Instruction -> Instruction -> bool.
Hypothesis independentb_sound : forall a b, independentb a b = true -> independent M a b.

(** Pull the next target instruction across only certified independent
    instructions. Removal preserves multiplicity, including duplicate actions. *)
Fixpoint move_front wanted source : option (list Instruction) :=
  match source with
  | [] => None
  | head :: tail =>
      if instruction_eq wanted head then Some tail else
      if independentb head wanted then
        match move_front wanted tail with Some rest => Some (head :: rest) | None => None end
      else None end.

Lemma move_front_sound wanted source rest : move_front wanted source = Some rest ->
  schedule_certificate M source (wanted :: rest).
Proof.
  revert rest; induction source as [|head tail IH]; intros rest CHECK; [discriminate|].
  cbn [move_front] in CHECK; destruct (instruction_eq wanted head) as [SAME|DIFFERENT].
  - subst head; injection CHECK as SAME; subst rest; constructor.
  - destruct (independentb head wanted) eqn:INDEPENDENT; try discriminate.
    destruct (move_front wanted tail) as [remaining|] eqn:MOVED; try discriminate.
    injection CHECK as SAME; subst rest.
    eapply certificate_trans; [apply certificate_head; apply IH; reflexivity|].
    apply certificate_swap; apply independentb_sound; exact INDEPENDENT.
Qed.

Fixpoint check_schedule source target : bool :=
  match target with
  | [] => match source with [] => true | _ => false end
  | wanted :: tail => match move_front wanted source with
      Some rest => check_schedule rest tail | None => false end end.

Theorem check_schedule_sound source target : check_schedule source target = true ->
  schedule_certificate M source target.
Proof.
  revert source; induction target as [|wanted tail IH]; intros source CHECK.
  - destruct source; [constructor|discriminate].
  - cbn [check_schedule] in CHECK.
    destruct (move_front wanted source) as [rest|] eqn:MOVED; try discriminate.
    eapply certificate_trans; [apply move_front_sound; exact MOVED|].
    apply certificate_head; apply IH; exact CHECK.
Qed.

Theorem check_schedule_preserves source target initial final :
  check_schedule source target = true -> schedule_invariant M initial ->
  schedule_run M source initial final ->
  exists candidate, schedule_run M target initial candidate /\ state_equivalent M final candidate.
Proof.
  intros CHECK; apply certified_schedule_preserves, check_schedule_sound; exact CHECK.
Qed.

Lemma check_schedule_identity source : check_schedule source source = true.
Proof.
  induction source as [|head tail IH]; [reflexivity|].
  cbn [check_schedule move_front]; destruct (instruction_eq head head); [exact IH|congruence].
Qed.
End CHECKER.

Lemma schedule_certificate_permutation {S Instruction} (M : scheduling_model S Instruction) source target :
  schedule_certificate M source target -> Permutation source target.
Proof.
  intro CERT; induction CERT; [reflexivity|constructor; assumption|apply perm_swap|eapply perm_trans; eauto].
Qed.

Print Assumptions check_schedule_sound.
Print Assumptions check_schedule_preserves.
