From Stdlib Require Import Bool.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition.
Set Implicit Arguments.

(** A branch may use facts about a refused answer only when those facts have
    their own certificate. Ordinary conservative conditions provide no such
    negative evidence. Neither outcome is assumed to be a logical complement. *)
Record readonly_classifier {S} (H : guard_host S)
  (domain yes_property no_property : S -> Prop) (probe : check H) := ReadonlyClassifier {
  classifier_safe : forall entry, domain entry -> check_safe H probe entry;
  classifier_available : forall entry, domain entry ->
    exists answer checked, checks H probe entry answer checked;
  classifier_sound : forall entry answer checked,
    domain entry -> checks H probe entry answer checked ->
    checked = entry /\ (if answer then yes_property entry else no_property entry)
}.

Record readonly_branch_algebra {S} (H : guard_host S) := ReadonlyBranchAlgebra {
  branch_check : check H -> check H -> check H -> check H;
  branch_check_exact : forall probe yes no entry answer checked,
    checks H (branch_check probe yes no) entry answer checked <->
    exists choice middle, checks H probe entry choice middle /\
      checks H (if choice then yes else no) middle answer checked;
  branch_check_safe : forall probe yes no entry,
    check_safe H probe entry ->
    (forall choice middle, checks H probe entry choice middle ->
      check_safe H (if choice then yes else no) middle) ->
    check_safe H (branch_check probe yes no) entry
}.

Definition condition_classifier S (H : guard_host S) domain premise probe
  (CERT : readonly_condition H domain premise probe) :
  readonly_classifier H domain premise (fun _ => True) probe.
Proof.
  constructor; [exact (readonly_safe CERT)|exact (readonly_available CERT)|].
  intros entry answer checked DOMAIN RUN.
  destruct (readonly_sound CERT entry answer checked DOMAIN RUN) as [SAME SOUND].
  split; [exact SAME|destruct answer; [apply SOUND; reflexivity|exact I]].
Defined.

Definition classifier_condition S (H : guard_host S) domain yes_property no_property probe
  (CERT : readonly_classifier H domain yes_property no_property probe) :
  readonly_condition H domain yes_property probe.
Proof.
  constructor; [exact (classifier_safe CERT)|exact (classifier_available CERT)|].
  intros entry answer checked DOMAIN RUN.
  destruct (classifier_sound CERT entry answer checked DOMAIN RUN) as [SAME SOUND].
  split; [exact SAME|intro ACCEPT; subst answer; exact SOUND].
Defined.

Definition readonly_true_condition S (H : guard_host S) (A : readonly_check_algebra H) domain premise
  (ENTAILS : forall entry, domain entry -> premise entry) :
  readonly_condition H domain premise (constant_check A true).
Proof.
  eapply readonly_condition_entails; [apply readonly_constant_condition|].
  intros entry DOMAIN _; apply ENTAILS; exact DOMAIN.
Defined.
Definition readonly_false_condition S (H : guard_host S) (A : readonly_check_algebra H) domain premise :
  readonly_condition H domain premise (constant_check A false).
Proof.
  constructor.
  - intros; apply constant_check_safe.
  - intros entry DOMAIN; exists false, entry; apply constant_check_exact; auto.
  - intros entry answer checked DOMAIN RUN; apply constant_check_exact in RUN as [FALSE SAME].
    split; [exact SAME|intro ACCEPT; congruence].
Defined.

Definition branch_readonly_conditions S (H : guard_host S) (B : readonly_branch_algebra H)
  domain yes_property no_property premise probe yes no
  (PROBE : readonly_classifier H domain yes_property no_property probe)
  (YES : readonly_condition H (fun entry => domain entry /\ yes_property entry) premise yes)
  (NO : readonly_condition H (fun entry => domain entry /\ no_property entry) premise no) :
  readonly_condition H domain premise (branch_check B probe yes no).
Proof.
  constructor.
  - intros entry DOMAIN; apply branch_check_safe; [apply (classifier_safe PROBE); exact DOMAIN|].
    intros choice middle RUN.
    destruct (classifier_sound PROBE entry choice middle DOMAIN RUN) as [SAME FACT]; subst middle.
    destruct choice; [apply (readonly_safe YES)|apply (readonly_safe NO)]; auto.
  - intros entry DOMAIN.
    destruct (classifier_available PROBE entry DOMAIN) as [choice [middle RUN]].
    destruct (classifier_sound PROBE entry choice middle DOMAIN RUN) as [SAME FACT]; subst middle.
    destruct choice.
    + destruct (readonly_available YES entry (conj DOMAIN FACT)) as [answer [checked NEXT]].
      exists answer, checked; apply branch_check_exact; exists true, entry; auto.
    + destruct (readonly_available NO entry (conj DOMAIN FACT)) as [answer [checked NEXT]].
      exists answer, checked; apply branch_check_exact; exists false, entry; auto.
  - intros entry answer checked DOMAIN RUN; apply branch_check_exact in RUN.
    destruct RUN as [choice [middle [PROBE_RUN NEXT]]].
    destruct (classifier_sound PROBE entry choice middle DOMAIN PROBE_RUN) as [SAME FACT]; subst middle.
    destruct choice; [exact (readonly_sound YES entry answer checked (conj DOMAIN FACT) NEXT)|
      exact (readonly_sound NO entry answer checked (conj DOMAIN FACT) NEXT)].
Defined.

Print Assumptions condition_classifier.
Print Assumptions classifier_condition.
Print Assumptions readonly_true_condition.
Print Assumptions readonly_false_condition.
Print Assumptions branch_readonly_conditions.
