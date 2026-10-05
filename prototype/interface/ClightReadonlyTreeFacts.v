From Guard Require Import ClightCondition ClightPureExpr.
From GuardInterface Require Import ClightReadonlyRewrite.
Set Implicit Arguments.

(** A completed path plus determinacy of every node justifies all-path safety
    for a tree of scalar expressions. Loads need their own safety certificate. *)
Lemma pure_decision_run_safe tree : pure_tree tree -> forall entry answer,
  decision_run entry tree answer -> readonly_tree_safe entry tree.
Proof.
  intro PURE; induction PURE as [known|a yes no SCALAR YES IHY NO IHN]; intros entry answer RUN.
  - constructor.
  - inversion RUN; subst; cbn [readonly_tree_safe]; split.
    + eexists; eassumption.
    + intros other TEST.
      match goal with CHECK : expression_test a entry ?choice |- _ =>
        pose proof (pure_test_determinate SCALAR TEST CHECK) as SAME; subst other;
        destruct choice end; eauto.
Qed.

Print Assumptions pure_decision_run_safe.
