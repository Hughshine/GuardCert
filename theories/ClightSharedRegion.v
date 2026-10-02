From Stdlib Require Import List ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import Values Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightFiniteRegion
  ClightRegionRewrite ClightRegionRule CompCertMemoryEquivalence.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A switch catches check refusal; a surrounding one-shot loop catches the
    successful candidate's continue. Both paths then leave through the loop's
    increment break. This shares the fallback without labels or scratch. *)
Definition singleton_switch body :=
  Sswitch (Econst_int Int.zero type_int32s) (LScons (Some 0) body LSnil).
Definition shared_guarded_statement guard candidate source :=
  Sloop (Ssequence (singleton_switch
    (tree_statement guard (Ssequence candidate Scontinue) Sbreak)) source) Sbreak.

Lemma singleton_switch_execution fe ge e le m body le' m' out :
  exec_stmt fe ge e le m body E0 le' m' out ->
  exec_stmt fe ge e le m (singleton_switch body) E0 le' m' (outcome_switch out).
Proof.
  intro RUN; unfold singleton_switch; eapply exec_Sswitch with (v := Vint Int.zero) (n := 0).
  - constructor.
  - reflexivity.
  - cbn [select_switch seq_of_labeled_statement].
    destruct out; try (eapply exec_Sseq_2; [exact RUN|discriminate]).
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RUN|constructor].
Qed.

Theorem shared_guarded_statement_execution fe ge e le m guard flag candidate source le' m' :
  decision_run (Entry ge e le m) guard flag ->
  exec_stmt fe ge e le m (if flag then candidate else source) E0 le' m' Out_normal ->
  exec_stmt fe ge e le m (shared_guarded_statement guard candidate source) E0 le' m' Out_normal.
Proof.
  intros CHECK RUN; unfold shared_guarded_statement; destruct flag.
  - eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (out1 := Out_continue) (out2 := Out_break).
    + eapply exec_Sseq_2; [|discriminate].
      change Out_continue with (outcome_switch Out_continue).
      apply singleton_switch_execution.
      eapply decision_fragment_run; [exact CHECK|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact RUN|constructor].
    + constructor.
    + constructor.
    + constructor.
  - eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (out1 := Out_normal) (out2 := Out_break).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m); [|exact RUN].
      change Out_normal with (outcome_switch Out_break).
      apply singleton_switch_execution.
      eapply decision_fragment_run; [exact CHECK|constructor].
    + constructor.
    + constructor.
    + constructor.
Qed.

Theorem shared_guarded_region_contract source guard candidate :
  guarded_fragment_contract source guard candidate ->
  region_contract source (shared_guarded_statement guard candidate source).
Proof.
  intros CONTRACT temps p e le m le' m' SOURCE f k.
  destruct (CONTRACT temps p e le m le' m' SOURCE) as [flag [CHECK CANDIDATE]].
  assert (SELECTED : exists target_memory,
    exec_stmt (adapter_entry temps) (globalenv p) e le m
      (if flag then candidate else source) E0 le' target_memory Out_normal /\
    memory_equivalent m' target_memory).
  { destruct flag; [apply CANDIDATE; reflexivity|].
    exists m'; split; [exact SOURCE|apply memory_equivalent_refl]. }
  destruct SELECTED as [target_memory [RUN SAME]].
  pose proof (@shared_guarded_statement_execution (adapter_entry temps) (globalenv p) e le m
    guard flag candidate source le' target_memory CHECK RUN) as TARGET.
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ TARGET f k)
    as [next [STEPS EXIT]]; inversion EXIT; subst next.
  exists target_memory; auto.
Qed.

Definition shared_generated_region {source candidate} (rule : encoded_region_rule source candidate) :=
  shared_guarded_statement (generated_region_tree rule) candidate source.
Theorem shared_encoded_region_rule_sound source candidate (rule : encoded_region_rule source candidate) :
  region_contract source (shared_generated_region rule).
Proof. apply shared_guarded_region_contract, encoded_region_rule_guarded. Qed.

Lemma shared_guarded_statement_label_free guard candidate source :
  label_free candidate = true -> label_free source = true ->
  label_free (shared_guarded_statement guard candidate source) = true.
Proof.
  intros CANDIDATE SOURCE; unfold shared_guarded_statement, singleton_switch.
  cbn [label_free labels_free].
  rewrite tree_statement_label_free; cbn [label_free]; rewrite ?CANDIDATE, ?SOURCE; reflexivity.
Qed.

Print Assumptions shared_guarded_statement_execution.
Print Assumptions shared_encoded_region_rule_sound.
