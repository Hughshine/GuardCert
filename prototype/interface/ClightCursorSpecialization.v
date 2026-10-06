From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint.
From GuardInterface Require Import ClightQuietDeterminacy ClightCheckPlan.
Import ListNotations.
Set Implicit Arguments.

(** Replace only reads of one private cursor. All type annotations are kept;
    no source temporary is assigned and no memory operation is executed. *)
Fixpoint cursor_expression_at cursor index expression :=
  match expression with
  | Etempvar identifier ty => if peq identifier cursor then Econst_int (Int.repr index) ty else expression
  | Ederef child ty => Ederef (cursor_expression_at cursor index child) ty
  | Eaddrof child ty => Eaddrof (cursor_expression_at cursor index child) ty
  | Eunop op child ty => Eunop op (cursor_expression_at cursor index child) ty
  | Ebinop op first second ty => Ebinop op (cursor_expression_at cursor index first) (cursor_expression_at cursor index second) ty
  | Ecast child ty => Ecast (cursor_expression_at cursor index child) ty
  | Efield child field ty => Efield (cursor_expression_at cursor index child) field ty
  | _ => expression
  end.
Lemma cursor_expression_at_type cursor index expression :
  typeof (cursor_expression_at cursor index expression)=typeof expression.
Proof. destruct expression; cbn; try reflexivity; destruct (peq i cursor); reflexivity. Qed.

Lemma cursor_expression_at_fresh cursor index expression :
  ~ In cursor (expression_temps expression) ->
  cursor_expression_at cursor index expression = expression.
Proof.
  induction expression; cbn [expression_temps cursor_expression_at]; intro FRESH; try reflexivity;
    try (rewrite IHexpression by assumption; reflexivity).
  - destruct (peq i cursor); [subst; exfalso; apply FRESH; cbn; auto|reflexivity].
  - rewrite IHexpression1,IHexpression2; [reflexivity| |]; intro MEMBER; apply FRESH; apply in_or_app; auto.
Qed.

(** A value/probe established in the logical unfolding is realized by the
    same runtime expression when its cursor has the corresponding word. *)
Theorem cursor_expression_at_execution ge locals temps memory cursor index expression :
  temps ! cursor = Some (Vint (Int.repr index)) ->
  (forall value, eval_expr ge locals temps memory (cursor_expression_at cursor index expression) value ->
    eval_expr ge locals temps memory expression value) /\
  (forall block offset field, eval_lvalue ge locals temps memory (cursor_expression_at cursor index expression) block offset field ->
    eval_lvalue ge locals temps memory expression block offset field).
Proof.
  intro CURSOR; induction expression; cbn [cursor_expression_at] in *;
    try (destruct IHexpression as [VALUE ADDRESS]);
    try (destruct IHexpression1 as [FIRST FIRST_ADDRESS]; destruct IHexpression2 as [SECOND SECOND_ADDRESS]).
  all: try solve [split; intros; assumption].
  all: try solve [destruct (peq i cursor) as [SAME|OTHER];
    [subst i; split; intros;
      first [solve [eliminate_impossible_lvalue]|
        match goal with RUN : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => inversion RUN; subst end;
        eliminate_impossible_lvalue; constructor; exact CURSOR]
    |split; intros; assumption]].
  all: split; intros.
  all: match goal with
  | RUN : eval_expr _ _ _ _ _ _ |- _ => inversion RUN; subst
  | RUN : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion RUN; subst
  end.
  all: eliminate_impossible_lvalue.
  all: try match goal with RUN : eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ => inversion RUN; subst; clear RUN end.
  all: try match goal with RUN : eval_lvalue _ _ _ _ (Efield _ _ _) _ _ _ |- _ => inversion RUN; subst; clear RUN end.
  all: repeat rewrite cursor_expression_at_type in *.
  all: eauto 8 using eval_Ederef,eval_Eaddrof,eval_Eunop,eval_Ebinop,eval_Ecast,eval_Elvalue,eval_Efield_struct,eval_Efield_union.
Qed.

Lemma cursor_expression_at_reads cursor index expression identifier :
  In identifier (expression_temps (cursor_expression_at cursor index expression)) ->
  In identifier (expression_temps expression) /\ identifier <> cursor.
Proof.
  induction expression; cbn [cursor_expression_at expression_temps] in *; try contradiction;
    try exact IHexpression.
  - destruct (peq i cursor); [contradiction|intros [<-|[]]; split; [cbn; auto|congruence]].
  - intro MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + destruct (IHexpression1 MEMBER) as [READ OTHER]; split; [apply in_or_app; left; exact READ|exact OTHER].
    + destruct (IHexpression2 MEMBER) as [READ OTHER]; split; [apply in_or_app; right; exact READ|exact OTHER].
Qed.

Theorem cursor_expression_test_transport entry cursor index expression current choice :
  current ! cursor = Some (Vint (Int.repr index)) ->
  temp_agree (expression_temps (cursor_expression_at cursor index expression)) (entry_temps entry) current ->
  expression_test (cursor_expression_at cursor index expression) entry choice ->
  expression_test expression (Entry (entry_ge entry) (entry_env entry) current (entry_memory entry)) choice.
Proof.
  intros CURSOR FRAME [value [EVAL BOOL]]; exists value; split.
  - apply (proj1 (@cursor_expression_at_execution (entry_ge entry) (entry_env entry) current
      (entry_memory entry) cursor index expression CURSOR)).
    eapply expression_temp_transport with (live:=expression_temps (cursor_expression_at cursor index expression));
      [unfold expression_scope,incl; auto|exact FRAME|exact EVAL].
  - cbn [entry_memory]; rewrite <- (cursor_expression_at_type cursor index expression); exact BOOL.
Qed.

Fixpoint cursor_tree_at cursor index tree :=
  match tree with
  | Decision answer => Decision answer
  | Test expression yes no => Test (cursor_expression_at cursor index expression)
      (cursor_tree_at cursor index yes) (cursor_tree_at cursor index no)
  end.

Lemma cursor_tree_at_bind cursor index tree yes no :
  cursor_tree_at cursor index (decision_bind tree yes no) =
    decision_bind (cursor_tree_at cursor index tree) (cursor_tree_at cursor index yes) (cursor_tree_at cursor index no).
Proof.
  induction tree as [answer|expression first IHfirst second IHsecond]; cbn [cursor_tree_at decision_bind];
    [destruct answer; reflexivity|rewrite IHfirst,IHsecond; reflexivity].
Qed.

Lemma cursor_tree_at_reads cursor index tree identifier :
  In identifier (check_plan_reads (tree_check_plan (cursor_tree_at cursor index tree))) ->
  In identifier (check_plan_reads (tree_check_plan tree)) /\ identifier <> cursor.
Proof.
  induction tree; cbn [cursor_tree_at tree_check_plan check_plan_reads]; [contradiction|].
  intro MEMBER; repeat rewrite in_app_iff in MEMBER; destruct MEMBER as [MEMBER|[MEMBER|MEMBER]].
  - destruct (@cursor_expression_at_reads cursor index condition identifier MEMBER) as [READ OTHER];
      split; [repeat rewrite in_app_iff; tauto|exact OTHER].
  - destruct (IHtree1 MEMBER) as [READ OTHER]; split; [repeat rewrite in_app_iff; tauto|exact OTHER].
  - destruct (IHtree2 MEMBER) as [READ OTHER]; split; [repeat rewrite in_app_iff; tauto|exact OTHER].
Qed.

Theorem cursor_tree_run_transport tree entry cursor index current answer :
  current ! cursor = Some (Vint (Int.repr index)) ->
  temp_agree (check_plan_reads (tree_check_plan (cursor_tree_at cursor index tree))) (entry_temps entry) current ->
  decision_run entry (cursor_tree_at cursor index tree) answer ->
  decision_run (Entry (entry_ge entry) (entry_env entry) current (entry_memory entry)) tree answer.
Proof.
  revert answer; induction tree; intros answer CURSOR FRAME RUN; cbn [cursor_tree_at] in RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; eapply run_test.
    + eapply cursor_expression_test_transport; [exact CURSOR| |eassumption].
      eapply temp_agree_weaken with
        (big:=check_plan_reads (tree_check_plan (cursor_tree_at cursor index (Test condition tree1 tree2))));
        [intros id MEMBER; cbn; repeat rewrite in_app_iff; tauto|exact FRAME].
    + destruct b.
      * apply IHtree1; [exact CURSOR| |assumption].
        eapply temp_agree_weaken with
          (big:=check_plan_reads (tree_check_plan (cursor_tree_at cursor index (Test condition tree1 tree2))));
          [intros id MEMBER; cbn; repeat rewrite in_app_iff; tauto|exact FRAME].
      * apply IHtree2; [exact CURSOR| |assumption].
        eapply temp_agree_weaken with
          (big:=check_plan_reads (tree_check_plan (cursor_tree_at cursor index (Test condition tree1 tree2))));
          [intros id MEMBER; cbn; repeat rewrite in_app_iff; tauto|exact FRAME].
Qed.

Print Assumptions cursor_expression_at_type.
Print Assumptions cursor_expression_at_fresh.
Print Assumptions cursor_expression_at_execution.
Print Assumptions cursor_expression_at_reads.
Print Assumptions cursor_expression_test_transport.
Print Assumptions cursor_tree_at_reads.
Print Assumptions cursor_tree_at_bind.
Print Assumptions cursor_tree_run_transport.
