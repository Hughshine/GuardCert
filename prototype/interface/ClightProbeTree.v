From Stdlib Require Import Bool List.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightSyntaxEquality ClightPureExpr.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyProbeTree ClightReadonlyRewrite
  ClightReadonlyLoadedTreeSynthesis ClightReadonlyProjectedCompiler.
Set Implicit Arguments.

Definition clight_probe_semantics : readonly_probe_semantics clight_entry expr :=
  @ReadonlyProbeSemantics clight_entry expr expression_test readonly_test_determinate.
Fixpoint import_clight_probe_tree tree : readonly_probe_tree expr :=
  match tree with Decision answer => ProbeDecision answer
  | Test expression yes no => ProbeTest expression (import_clight_probe_tree yes) (import_clight_probe_tree no) end.
Fixpoint compile_clight_probe_tree tree : decision_tree :=
  match tree with ProbeDecision answer => Decision answer
  | ProbeTest expression yes no => Test expression (compile_clight_probe_tree yes) (compile_clight_probe_tree no) end.

Lemma clight_probe_roundtrip tree : compile_clight_probe_tree (import_clight_probe_tree tree) = tree.
Proof. induction tree; cbn; [reflexivity|rewrite IHtree1, IHtree2; reflexivity]. Qed.

Lemma clight_probe_run tree : forall entry answer,
  decision_run entry (compile_clight_probe_tree tree) answer <-> probe_tree_run clight_probe_semantics entry tree answer.
Proof.
  induction tree as [value|expression yes YES no NO]; intros entry answer; cbn [compile_clight_probe_tree].
  - split; intro RUN; inversion RUN; subst; constructor.
  - split; intro RUN; inversion RUN; subst.
    + match goal with TEST : expression_test expression entry ?choice,
        LEAF : decision_run entry (if ?choice then _ else _) answer |- _ =>
        eapply probe_run_test; [exact TEST|]; destruct choice;
        [apply (proj1 (YES entry answer)); exact LEAF|apply (proj1 (NO entry answer)); exact LEAF] end.
    + match goal with TEST : probe_test clight_probe_semantics expression entry ?choice,
        LEAF : probe_tree_run clight_probe_semantics entry (if ?choice then _ else _) answer |- _ =>
        eapply run_test; [exact TEST|]; destruct choice;
        [apply (proj2 (YES entry answer)); exact LEAF|apply (proj2 (NO entry answer)); exact LEAF] end.
Qed.

Lemma clight_probe_safe tree : forall entry,
  readonly_tree_safe entry (compile_clight_probe_tree tree) <-> probe_tree_safe clight_probe_semantics tree entry.
Proof.
  induction tree as [value|expression yes YES no NO]; intro entry;
    cbn [readonly_tree_safe compile_clight_probe_tree probe_tree_safe clight_probe_semantics probe_test]; [reflexivity|].
  split; intros [DEFINED NEXT]; split; [exact DEFINED| |exact DEFINED|]; intros choice TEST; destruct choice.
  - apply (proj1 (YES entry)); exact (NEXT true TEST).
  - apply (proj1 (NO entry)); exact (NEXT false TEST).
  - apply (proj2 (YES entry)); exact (NEXT true TEST).
  - apply (proj2 (NO entry)); exact (NEXT false TEST).
Qed.

Definition clight_probe_compiler fe O (observe : fragment_observation -> O -> Prop) :
  readonly_probe_compiler (readonly_clight_host fe observe) clight_probe_semantics.
Proof.
  refine (@ReadonlyProbeCompiler clight_entry (readonly_clight_host fe observe) expr clight_probe_semantics
    compile_clight_probe_tree _ _).
  - intros tree entry answer checked; change (decision_run entry (compile_clight_probe_tree tree) answer /\ checked=entry <->
      probe_tree_run clight_probe_semantics entry tree answer /\ checked=entry).
    rewrite clight_probe_run; reflexivity.
  - intros tree entry; apply clight_probe_safe.
Defined.

Definition simplify_clight_guard tree :=
  compile_clight_probe_tree (simplify_probe_tree expression_eq (import_clight_probe_tree tree) nil).
Definition simplified_clight_condition fe O (observe : fragment_observation -> O -> Prop) domain premise tree
  (G : readonly_condition (readonly_clight_host fe observe) domain premise tree) :
  readonly_condition (readonly_clight_host fe observe) domain premise (simplify_clight_guard tree).
Proof.
  eapply (@simplified_probe_condition clight_entry (readonly_clight_host fe observe) expr clight_probe_semantics
    (clight_probe_compiler fe observe) expression_eq (import_clight_probe_tree tree) domain premise).
  change (readonly_condition (readonly_clight_host fe observe) domain premise
    (compile_clight_probe_tree (import_clight_probe_tree tree))).
  rewrite clight_probe_roundtrip; exact G.
Defined.

Definition simplified_projected_rule live source (rule : readonly_projected_clight_rule live source) :
  readonly_projected_clight_rule live source.
Proof.
  refine {| projected_candidate := projected_candidate rule;
    projected_guard := simplify_clight_guard (projected_guard rule);
    projected_domain := projected_domain rule; projected_premise := projected_premise rule;
    projected_source_writes := projected_source_writes rule;
    projected_source_write_bound := projected_source_write_bound rule |}.
  - intro temps; apply simplified_clight_condition, projected_rule_check.
  - exact (projected_rule_local rule).
  - exact (projected_rule_entry rule).
Defined.

Print Assumptions clight_probe_roundtrip.
Print Assumptions clight_probe_run.
Print Assumptions clight_probe_safe.
Print Assumptions clight_probe_compiler.
Print Assumptions simplified_clight_condition.
Print Assumptions simplified_projected_rule.
