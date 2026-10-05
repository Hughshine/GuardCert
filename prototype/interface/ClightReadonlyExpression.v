From compcert.common Require Import Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightTreeRewrite.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite.
Set Implicit Arguments.

(** Expressions plus finite readonly dispatch form commands of this host.
    The compiler lowers the dispatch around a concrete expression context. *)
Inductive checked_expression : Type :=
| Evaluate : expr -> checked_expression
| Dispatch : decision_tree -> checked_expression -> checked_expression -> checked_expression.
Inductive checked_expression_runs : checked_expression -> clight_entry -> val -> Prop :=
| evaluate_run : forall expression entry value,
    eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) expression value ->
    checked_expression_runs (Evaluate expression) entry value
| dispatch_run : forall tree yes no entry answer value,
    decision_run entry tree answer ->
    checked_expression_runs (if answer then yes else no) entry value ->
    checked_expression_runs (Dispatch tree yes no) entry value.
Definition readonly_expression_host : guard_host clight_entry.
Proof.
  refine {| code := checked_expression; check := decision_tree; observation := val;
    runs := checked_expression_runs;
    checks := fun tree entry answer checked => decision_run entry tree answer /\ checked = entry;
    check_safe := fun tree entry => readonly_tree_safe entry tree;
    select := Dispatch |}.
  intros tree yes no entry value; split.
  - intro RUN; inversion RUN; subst; eexists; eexists; split; [split; [eassumption|reflexivity]|eassumption].
  - intros [answer [checked [[TEST SAME] LEAF]]]; subst checked; econstructor; eassumption.
Defined.
Lemma readonly_expression_leaf expression entry value :
  runs readonly_expression_host (Evaluate expression) entry value <->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) expression value.
Proof. split; [intro RUN; inversion RUN; subst; assumption|intro EVAL; constructor; exact EVAL]. Qed.
Lemma fragment_condition_for_expression fe O (observe : fragment_observation -> O -> Prop) domain premise tree :
  readonly_condition (readonly_clight_host fe observe) domain premise tree ->
  readonly_condition readonly_expression_host domain premise tree.
Proof. intros [SAFE AVAILABLE SOUND]; constructor; assumption. Qed.

Record readonly_expression_rule (source : expr) := ReadonlyExpressionRule {
  expression_candidate : expr;
  expression_guard : decision_tree;
  expression_domain : clight_entry -> Prop;
  expression_premise : clight_entry -> Prop;
  expression_type_equal : typeof expression_candidate = typeof source;
  expression_check : readonly_condition readonly_expression_host expression_domain expression_premise expression_guard;
  expression_local : conditional_equivalence readonly_expression_host expression_domain expression_premise
    (Evaluate source) (Evaluate expression_candidate);
  expression_entry : forall ge locals le memory value, eval_expr ge locals le memory source value ->
    expression_domain (Entry ge locals le memory)
}.
Theorem readonly_expression_contract source (rule : readonly_expression_rule source) :
  expression_contract source (expression_guard rule) (expression_candidate rule).
Proof.
  split; [exact (expression_type_equal rule)|].
  intros ge locals le memory value SOURCE.
  pose proof (expression_entry rule SOURCE) as DOMAIN.
  destruct (readonly_available (expression_check rule) _ DOMAIN) as [answer [checked [TEST SAME]]]; subst checked.
  exists answer; split; [exact TEST|].
  intro ACCEPT.
  pose proof (readonly_sound (expression_check rule) _ _ _ DOMAIN (conj TEST eq_refl)) as [_ POSITIVE].
  pose proof (proj2 (@expression_local source rule (Entry ge locals le memory) value
    (conj DOMAIN (POSITIVE ACCEPT)))) as FORWARD.
  apply (proj1 (readonly_expression_leaf (expression_candidate rule) (Entry ge locals le memory) value)).
  apply FORWARD; apply (proj2 (readonly_expression_leaf source (Entry ge locals le memory) value)); exact SOURCE.
Qed.
Print Assumptions readonly_expression_host.
Print Assumptions fragment_condition_for_expression.
Print Assumptions readonly_expression_contract.
