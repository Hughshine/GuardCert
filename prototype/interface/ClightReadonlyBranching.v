From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyBranching
  ClightReadonlyRewrite ClightConditionComposition.
Set Implicit Arguments.

Definition clight_readonly_branch_algebra fe O (observe : fragment_observation -> O -> Prop) :
  readonly_branch_algebra (readonly_clight_host fe observe).
Proof.
  refine (@ReadonlyBranchAlgebra clight_entry (readonly_clight_host fe observe) decision_bind _ _).
  - intros probe yes no entry answer checked.
    change (decision_run entry (decision_bind probe yes no) answer /\ checked = entry <->
      exists choice middle, (decision_run entry probe choice /\ middle = entry) /\
        (decision_run middle (if choice then yes else no) answer /\ checked = middle)).
    split.
    + intros [RUN SAME]; destruct (@decision_bind_inv probe entry yes no answer RUN)
        as [choice [PREFIX LEAF]]; exists choice, entry; auto.
    + intros [choice [middle [[PREFIX SAME] [LEAF STATE]]]]; subst.
      split; [eapply decision_bind_run; [exact PREFIX|exact LEAF]|reflexivity].
  - intros probe yes no entry SAFE NEXT; apply readonly_decision_bind_safe; [exact SAFE|].
    intros answer RUN; apply (NEXT answer entry); split; [exact RUN|reflexivity].
Defined.

Definition readonly_expression_classifier fe O (observe : fragment_observation -> O -> Prop)
  expression domain yes_property no_property
  (DEFINED : forall entry, domain entry -> exists answer, expression_test expression entry answer)
  (YES : forall entry, domain entry -> expression_test expression entry true -> yes_property entry)
  (NO : forall entry, domain entry -> expression_test expression entry false -> no_property entry) :
  readonly_classifier (readonly_clight_host fe observe) domain yes_property no_property
    (Test expression (Decision true) (Decision false)).
Proof.
  constructor.
  - intros entry DOMAIN; split; [apply DEFINED; exact DOMAIN|intros answer RUN; destruct answer; exact I].
  - intros entry DOMAIN; destruct (DEFINED entry DOMAIN) as [answer RUN]; exists answer, entry; split; [|reflexivity].
    eapply run_test; [exact RUN|destruct answer; constructor].
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|].
    inversion RUN; subst.
    match goal with LEAF : decision_run _ (if ?choice then Decision true else Decision false) _ |- _ =>
      destruct choice; inversion LEAF; subst end.
    + apply YES; assumption.
    + apply NO; assumption.
Defined.

Print Assumptions clight_readonly_branch_algebra.
Print Assumptions readonly_expression_classifier.
