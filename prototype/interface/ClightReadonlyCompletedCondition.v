From Guard Require Import ClightCondition.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyLoadedTreeSynthesis.
Set Implicit Arguments.

(** Language service: actual expression determinacy turns a completed finite
    readonly path into safety of every reachable test. The domain author still
    proves completion and acceptance soundness; neither is a kernel axiom. *)
Definition readonly_completed_tree_condition fe O (observe : fragment_observation -> O -> Prop)
  (domain premise : clight_entry -> Prop) tree
  (COMPLETE : forall entry, domain entry -> exists answer, decision_run entry tree answer)
  (SOUND : forall entry, domain entry -> decision_run entry tree true -> premise entry) :
  readonly_condition (readonly_clight_host fe observe) domain premise tree.
Proof.
  constructor.
  - intros entry DOMAIN; destruct (COMPLETE entry DOMAIN) as [answer RUN].
    eapply readonly_decision_run_safe; exact RUN.
  - intros entry DOMAIN; destruct (COMPLETE entry DOMAIN) as [answer RUN].
    exists answer,entry; split; [exact RUN|reflexivity].
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    apply SOUND; assumption.
Defined.
Print Assumptions readonly_completed_tree_condition.
