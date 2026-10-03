From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightGuard ClightTempFootprint.
Import ListNotations.
Set Implicit Arguments.

Definition function_scope live f := incl (function_temps f) live.
Definition fundef_scope live fd := incl (fundef_temps fd) live.
Definition program_scope live p := forall name fd,
  In (name,Gfun fd) (prog_defs p) -> fundef_scope live fd.
Fixpoint continuation_scope live k : Prop :=
  match k with
  | Kstop => True
  | Kseq s k => statement_scope live s /\ continuation_scope live k
  | Kloop1 a b k | Kloop2 a b k =>
      statement_scope live a /\ statement_scope live b /\ continuation_scope live k
  | Kswitch k => continuation_scope live k
  | Kcall result f _ _ k => incl (optional_temp result) live /\ function_scope live f /\ continuation_scope live k
  end.
Definition state_scope live source :=
  match source with
  | State f s k _ _ _ => function_scope live f /\ statement_scope live s /\ continuation_scope live k
  | Callstate fd _ k _ => fundef_scope live fd /\ continuation_scope live k
  | Returnstate _ k _ => continuation_scope live k
  end.
Lemma function_scope_body live f : function_scope live f -> statement_scope live (fn_body f).
Proof. unfold function_scope, function_temps, statement_scope; eauto using scope_append_right. Qed.
Lemma function_scope_params live f : function_scope live f -> incl (var_names (fn_params f)) live.
Proof. unfold function_scope, function_temps; eauto using scope_append_left. Qed.
Lemma program_scope_computed p : program_scope (program_temps p) p.
Proof.
  intros name fd MEMBER id USED; unfold program_temps; apply in_flat_map.
  exists (name,Gfun fd); split; [exact MEMBER|].
  cbn [global_definition_temps]; right; exact USED.
Qed.
Lemma function_scope_lookup live p value fd : program_scope live p ->
  Genv.find_funct (globalenv p) value = Some fd -> fundef_scope live fd.
Proof.
  intros SCOPE LOOKUP; apply Genv.find_funct_inversion in LOOKUP as [name MEMBER]; eauto.
Qed.
Lemma function_scope_ptr_lookup live p block fd : program_scope live p ->
  Genv.find_funct_ptr (globalenv p) block = Some fd -> fundef_scope live fd.
Proof.
  intros SCOPE LOOKUP; apply Genv.find_funct_ptr_inversion in LOOKUP as [name MEMBER]; eauto.
Qed.
Lemma continuation_scope_call live k : continuation_scope live k -> continuation_scope live (call_cont k).
Proof. induction k; cbn; intuition. Qed.

Lemma scope_seq_cases live cases : cases_scope live cases ->
  statement_scope live (seq_of_labeled_statement cases).
Proof.
  induction cases; unfold cases_scope, statement_scope in *; cbn; intros S.
  - intros id BAD; contradiction.
  - unfold incl in *; intros id IN; apply in_app_iff in IN as [IN|IN].
    + apply S; apply in_or_app; auto.
    + apply IHcases; [apply scope_append_right with (a := statement_temps s); exact S|exact IN].
Qed.
Lemma scope_default_cases live cases : cases_scope live cases -> cases_scope live (select_switch_default cases).
Proof.
  induction cases; cbn; auto; intro S; destruct o; cbn; auto.
  apply IHcases; unfold cases_scope in *; cbn in S; eapply scope_append_right; exact S.
Qed.
Lemma scope_selected_case live n cases selected : cases_scope live cases ->
  select_switch_case n cases = Some selected -> cases_scope live selected.
Proof.
  revert selected; induction cases; cbn; intros selected S EQ; [discriminate|].
  destruct o; cbn in EQ.
  - destruct (zeq z n); [inversion EQ; subst; exact S|].
    eapply IHcases; [unfold cases_scope in *; cbn in S; eapply scope_append_right; exact S|exact EQ].
  - eapply IHcases; [unfold cases_scope in *; cbn in S; eapply scope_append_right; exact S|exact EQ].
Qed.
Lemma scope_select_switch live n cases : cases_scope live cases -> cases_scope live (select_switch n cases).
Proof.
  intro S; unfold select_switch; destruct (select_switch_case n cases) eqn:CASE;
    eauto using scope_selected_case, scope_default_cases.
Qed.

Local Hint Resolve scope_append_left scope_append_right scope_cons_tail scope_cons_head incl_app continuation_scope_call : core.
Lemma scope_empty live : incl ([] : list ident) live.
Proof. intros id BAD; contradiction. Qed.
Local Hint Resolve scope_empty : core.

Lemma find_label_scope :
  (forall s live lbl k found next, statement_scope live s -> continuation_scope live k ->
    find_label lbl s k = Some (found,next) -> statement_scope live found /\ continuation_scope live next) /\
  (forall cases live lbl k found next, cases_scope live cases -> continuation_scope live k ->
    find_label_ls lbl cases k = Some (found,next) -> statement_scope live found /\ continuation_scope live next).
Proof.
  apply ClightGuard.statement_cases_ind; intros; cbn in *; try discriminate.
  - unfold statement_scope in H1; cbn in H1.
    destruct (find_label lbl s (Kseq s0 k)) as [[a ak]|] eqn:LEFT.
    + inversion H3; subst; eapply (H live lbl (Kseq s0 k)).
      * unfold statement_scope; eauto.
      * cbn; split; [unfold statement_scope; eauto|exact H2].
      * exact LEFT.
    + eapply (H0 live lbl k); [unfold statement_scope; eauto|exact H2|exact H3].
  - unfold statement_scope in H1; cbn in H1.
    destruct (find_label lbl s k) as [[a ak]|] eqn:LEFT.
    + inversion H3; subst; eapply (H live lbl k); [unfold statement_scope; eauto|exact H2|exact LEFT].
    + eapply (H0 live lbl k); [unfold statement_scope; eauto|exact H2|exact H3].
  - unfold statement_scope in H1; cbn in H1.
    destruct (find_label lbl s (Kloop1 s s0 k)) as [[a ak]|] eqn:LEFT.
    + inversion H3; subst; eapply (H live lbl (Kloop1 s s0 k)).
      * unfold statement_scope; eauto.
      * cbn; repeat split; [unfold statement_scope; eauto|unfold statement_scope; eauto|exact H2].
      * exact LEFT.
    + eapply (H0 live lbl (Kloop2 s s0 k)).
      * unfold statement_scope; eauto.
      * cbn; repeat split; [unfold statement_scope; eauto|unfold statement_scope; eauto|exact H2].
      * exact H3.
  - eapply (H live lbl (Kswitch k)); [unfold cases_scope, statement_scope in *; cbn in *; eauto|exact H1|exact H2].
  - destruct (ident_eq lbl l).
    + inversion H2; subst; auto.
    + eapply (H live lbl k); eauto.
  - unfold cases_scope in H1; cbn in H1.
    destruct (find_label lbl s (Kseq (seq_of_labeled_statement l) k)) as [[a ak]|] eqn:LEFT.
    + inversion H3; subst; eapply (H live lbl (Kseq (seq_of_labeled_statement l) k)).
      * unfold statement_scope; eauto.
      * cbn; split; [apply scope_seq_cases; unfold cases_scope; eauto|exact H2].
      * exact LEFT.
    + eapply (H0 live lbl k); [unfold cases_scope; eauto|exact H2|exact H3].
Qed.

Theorem step_preserves_temp_scope live p temps before events after :
  program_scope live p -> state_scope live before ->
  adapter_step temps (globalenv p) before events after -> state_scope live after.
Proof.
  intros PROGRAM SCOPE STEP; inversion STEP; subst;
    cbn [state_scope] in SCOPE |- *;
    unfold statement_scope in *; cbn [statement_temps optional_expression_temps] in *;
    try (destruct SCOPE as [FUNC [CODE CONT]]);
    try solve [cbn [continuation_scope] in *; unfold statement_scope in *; intuition eauto 5].
  - repeat split; auto; [eapply function_scope_lookup; eauto|].
    cbn; repeat split; auto; eauto.
  - destruct b; repeat split; eauto.
  - repeat split; auto. apply scope_seq_cases, scope_select_switch.
    unfold cases_scope; eauto.
  - destruct (proj1 find_label_scope (fn_body f) live lbl (call_cont k) s' k'
      (function_scope_body FUNC) (continuation_scope_call live k CONT) H) as [BODY K].
    repeat split; assumption.
Qed.

Print Assumptions step_preserves_temp_scope.
