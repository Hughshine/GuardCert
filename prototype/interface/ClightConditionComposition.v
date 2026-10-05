From compcert.common Require Import Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ClightReadonlyRewrite.
Set Implicit Arguments.

Lemma readonly_decision_bind_safe tree : forall entry yes no,
  readonly_tree_safe entry tree ->
  (forall answer, decision_run entry tree answer -> readonly_tree_safe entry (if answer then yes else no)) ->
  readonly_tree_safe entry (decision_bind tree yes no).
Proof.
  induction tree as [answer|expression left LEFT right RIGHT]; intros entry yes no SAFE LEAVES;
    cbn [decision_bind readonly_tree_safe] in *.
  - apply LEAVES; constructor.
  - destruct SAFE as [DEFINED SAFE]; split; [exact DEFINED|].
    intros answer TEST; destruct answer.
    + apply LEFT; [apply SAFE with (accepted := true); exact TEST|].
      intros result RUN; apply LEAVES; eapply run_test with (b := true); eassumption.
    + apply RIGHT; [apply SAFE with (accepted := false); exact TEST|].
      intros result RUN; apply LEAVES; eapply run_test with (b := false); eassumption.
Qed.
Lemma decision_bind_identity tree : decision_bind tree (Decision true) (Decision false) = tree.
Proof. induction tree as [answer|expression left LEFT right RIGHT]; cbn [decision_bind];
  [destruct answer; reflexivity|rewrite LEFT, RIGHT; reflexivity]. Qed.

Definition clight_readonly_check_algebra fe O (observe : fragment_observation -> O -> Prop) :
  readonly_check_algebra (readonly_clight_host fe observe).
Proof.
  refine (@ReadonlyCheckAlgebra clight_entry (readonly_clight_host fe observe) Decision
    (fun first second => decision_bind first second (Decision false)) _ _ _ _).
  - intros; exact I.
  - intros value entry answer checked; change (decision_run entry (Decision value) answer /\ checked = entry <->
      answer = value /\ checked = entry).
    split; [intros [RUN SAME]; inversion RUN; auto|intros [SAME STATE]; subst; split; [constructor|reflexivity]].
  - intros first second entry answer checked.
    change (decision_run entry (decision_bind first second (Decision false)) answer /\ checked = entry <->
      (exists middle, (decision_run entry first true /\ middle = entry) /\
        (decision_run middle second answer /\ checked = middle)) \/
      (answer = false /\ decision_run entry first false /\ checked = entry)).
    split.
    + intros [RUN SAME]; destruct (@decision_bind_inv first entry second (Decision false) answer RUN)
        as [accepted [PREFIX LEAF]]; destruct accepted.
      * left; exists entry; auto.
      * inversion LEAF; subst; right; auto.
    + intros [[middle [[PREFIX SAME] [LEAF STATE]]]|[FALSE [PREFIX STATE]]]; subst.
      * split; [eapply decision_bind_run; [exact PREFIX|exact LEAF]|reflexivity].
      * split; [eapply decision_bind_run; [exact PREFIX|constructor]|reflexivity].
  - intros first second entry SAFE NEXT; apply readonly_decision_bind_safe; [exact SAFE|].
    intros answer RUN; destruct answer; [apply (NEXT entry); split; [exact RUN|reflexivity]|exact I].
Defined.

(** A rule author may submit expression definedness and its positive meaning
    on a domain established by preceding checks. The expression stays actual
    Clight syntax; no total mathematical evaluator is assumed. *)
Definition readonly_expression_condition fe O (observe : fragment_observation -> O -> Prop)
  expression domain premise
  (DEFINED : forall entry, domain entry -> exists answer, expression_test expression entry answer)
  (SOUND : forall entry, domain entry -> expression_test expression entry true -> premise entry) :
  readonly_condition (readonly_clight_host fe observe) domain premise
    (Test expression (Decision true) (Decision false)).
Proof.
  constructor.
  - intros entry DOMAIN; split; [apply DEFINED; exact DOMAIN|intros answer RUN; destruct answer; exact I].
  - intros entry DOMAIN; destruct (DEFINED entry DOMAIN) as [answer RUN]; exists answer, entry; split; [|reflexivity].
    eapply run_test; [exact RUN|destruct answer; constructor].
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    inversion RUN; subst.
    match goal with LEAF : decision_run _ (if ?choice then Decision true else Decision false) true |- _ =>
      destruct choice; inversion LEAF; subst end.
    apply SOUND; assumption.
Defined.
Print Assumptions readonly_decision_bind_safe.
Print Assumptions decision_bind_identity.
Print Assumptions clight_readonly_check_algebra.
Print Assumptions readonly_expression_condition.
