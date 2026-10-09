From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightPureExpr ClightTempFrame.
From GuardInterface Require Import ClightReadonlyRewrite ClightCheckPlan ClightCheckPlanFrame.
Set Implicit Arguments.

(** Factor two alternatives without copying their fallback statement into
    each decision leaf. The accepted branch retests the first readonly tree
    to distinguish the empty outer case from the replacement case. *)
Definition readonly_alternative_plan outer inner :=
  tree_check_plan(decision_bind outer(Decision true)inner).
Definition readonly_alternative_yes outer replacement :=tree_statement outer Sskip replacement.
Definition readonly_alternative_statement outer inner result replacement original :=
  check_plan_guarded_statement(readonly_alternative_plan outer inner)result
    (readonly_alternative_yes outer replacement)original.

Lemma readonly_alternative_selected_execution fe ge locals temps memory outer inner replacement original after final :
  exec_stmt fe ge locals temps memory
    (tree_statement outer Sskip(tree_statement inner replacement original))E0 after final Out_normal ->
  exists answer,decision_run(Entry ge locals temps memory)
    (check_plan_tree(readonly_alternative_plan outer inner))answer /\
    exec_stmt fe ge locals temps memory
      (if answer then readonly_alternative_yes outer replacement else original)E0 after final Out_normal.
Proof.
  intro SELECT.
  change(clight_fragment_run fe(tree_statement outer Sskip(tree_statement inner replacement original))
    (Entry ge locals temps memory)(FragmentObservation E0 after final Out_normal))in SELECT.
  destruct(proj1(@readonly_tree_execution_exact fe outer Sskip(tree_statement inner replacement original)
    (Entry ge locals temps memory)(FragmentObservation E0 after final Out_normal))SELECT)
    as [empty[OUTER BRANCH]].
  destruct empty.
  - exists true; split.
    + unfold readonly_alternative_plan; rewrite tree_check_plan_spec.
      eapply decision_bind_run; [exact OUTER|constructor].
    + unfold readonly_alternative_yes; eapply decision_fragment_run with(b:=true); [exact OUTER|exact BRANCH].
  - destruct(proj1(@readonly_tree_execution_exact fe inner replacement original
      (Entry ge locals temps memory)(FragmentObservation E0 after final Out_normal))BRANCH)
      as [accepted[INNER LEAF]].
    exists accepted; split.
    + unfold readonly_alternative_plan; rewrite tree_check_plan_spec.
      eapply decision_bind_run; [exact OUTER|exact INNER].
    + destruct accepted; [|exact LEAF].
      unfold readonly_alternative_yes; eapply decision_fragment_run with(b:=false); [exact OUTER|exact LEAF].
Qed.

Theorem readonly_alternative_planned_execution fe ge locals temps memory outer inner result live replacement original after final :
  check_plan_resources(readonly_alternative_plan outer inner)result live
    (readonly_alternative_yes outer replacement)original=true ->
  exec_stmt fe ge locals temps memory
    (tree_statement outer Sskip(tree_statement inner replacement original))E0 after final Out_normal ->
  exists exit,exec_stmt fe ge locals temps memory
    (readonly_alternative_statement outer inner result replacement original)E0 exit final Out_normal /\
    temp_agree live after exit.
Proof.
  intros RESOURCES SOURCE.
  destruct(check_plan_resources_sound _ _ _ _ _ RESOURCES)as [YES[NO PRIVATE]].
  destruct(@readonly_alternative_selected_execution fe ge locals temps memory outer inner replacement original after final SOURCE)as [answer[CHECK BRANCH]].
  unfold readonly_alternative_statement.
  eapply check_plan_guarded_normal_execution; eassumption.
Qed.

Print Assumptions readonly_alternative_selected_execution.
Print Assumptions readonly_alternative_planned_execution.
