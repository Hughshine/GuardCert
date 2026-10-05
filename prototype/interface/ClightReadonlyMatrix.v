From Stdlib Require Import Bool List.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import Events Errors Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep Csyntax Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightGuard ClightCondition ClightPureExpr ClightRegionProgress
  ClightStructuredProgress ClightCountedLoop ClightFrontendLoopProtocol ClightLoopSyntax ClightMatrixStore
  ClightMatrixGuard ClightMatrixLoops ClightMatrixRegion ClightMatrixSelector CompCertIndexSchedule.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyTreeFacts ClightQuietDeterminacy ClightLoopBridge ClightReadonlyCompiler.
Import ListNotations.
Set Implicit Arguments.

Definition readonly_matrix_domain d entry :=
  matrix_guard_domain (matrix_row d) (matrix_bound d) (matrix_inner_bound d) entry /\
  quiet_source_completion (matrix_described_source d) entry.
Definition readonly_matrix_premise d :=
  matrix_guard_property (matrix_row d) (matrix_bound d) (matrix_inner_bound d) tt.

Lemma described_matrix_source_quiet source d (CERT : matrix_certificate source d) :
  quiet_statement (matrix_described_source d) = true.
Proof.
  assert (OUTER : quiet_statement (matrix_outer_body d) = true).
  { apply flatten_quiet_certificate; rewrite (matrix_outer_bound CERT).
    constructor; [reflexivity|constructor; [|constructor]].
    cbn [frontend_counted_loop quiet_statement counter_increment].
    rewrite (@matrix_body_quiet (described_array d) (matrix_row d) (matrix_column d)
      (matrix_inner_body d) (matrix_body_bound CERT)); reflexivity. }
  cbn [matrix_described_source frontend_counted_loop quiet_statement counter_increment].
  rewrite OUTER; reflexivity.
Qed.

Lemma described_matrix_source_normal source d (CERT : matrix_certificate source d) :
  normal_statement (matrix_described_source d) = true.
Proof.
  cbn [matrix_described_source frontend_counted_loop normal_statement quiet_statement counter_increment].
  pose proof (described_matrix_source_quiet CERT) as QUIET.
  cbn [matrix_described_source frontend_counted_loop quiet_statement counter_increment] in QUIET.
  exact QUIET.
Qed.

Lemma described_matrix_target_quiet d : quiet_statement (matrix_described_target d) = true.
Proof.
  reflexivity.
Qed.

Definition readonly_matrix_condition fe d :
  readonly_condition (readonly_clight_host fe (@eq fragment_observation)) (readonly_matrix_domain d)
    (readonly_matrix_premise d) (matrix_guard_tree (matrix_row d) (matrix_bound d) (matrix_inner_bound d)).
Proof.
  constructor.
  - intros entry [DOMAIN COMPLETE].
    eapply pure_decision_run_safe; [apply matrix_guard_tree_pure|apply matrix_guard_tree_run; exact DOMAIN].
  - intros entry [DOMAIN COMPLETE].
    exists (matrix_guard_accept (matrix_row d) (matrix_bound d) (matrix_inner_bound d) tt entry), entry.
    split; [apply matrix_guard_tree_run; exact DOMAIN|reflexivity].
  - intros entry accepted checked [DOMAIN COMPLETE] [RUN SAME]; split; [exact SAME|]; intro ACCEPT.
    assert (RESULT : accepted = matrix_guard_accept (matrix_row d) (matrix_bound d) (matrix_inner_bound d) tt entry).
    { eapply pure_tree_determinate; [apply matrix_guard_tree_pure|exact RUN|apply matrix_guard_tree_run; exact DOMAIN]. }
    apply matrix_guard_accept_sound; [exact DOMAIN|congruence].
Defined.

Lemma readonly_matrix_forward source d (CERT : matrix_certificate source d) fe entry observed :
  readonly_matrix_premise d entry ->
  clight_fragment_run fe (matrix_described_source d) entry observed ->
  clight_fragment_run fe (matrix_described_target d) entry observed.
Proof.
  destruct observed as [trace temps final out]; intros [ZERO [TWO INNER_TWO]] RUN.
  pose proof (@quiet_execution_silent fe (entry_ge entry) (entry_env entry) (entry_temps entry)
    (entry_memory entry) (matrix_described_source d) trace temps final out RUN
    (described_matrix_source_quiet CERT)) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe (entry_ge entry) (entry_env entry)
    (matrix_described_source d) (described_matrix_source_normal CERT)
    (entry_temps entry) (entry_memory entry) E0 temps final out RUN) as NORMAL; subst out.
  destruct (@matrix_source_decode fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (described_array d) (matrix_row d) (matrix_bound d) (matrix_column d) (matrix_inner_bound d)
    (matrix_inner_body d) (matrix_outer_body d) temps final
    (matrix_distinct_row_bound CERT) (matrix_distinct_row_column CERT) (matrix_distinct_bound_column CERT)
    (matrix_distinct_row_inner_bound CERT) (matrix_distinct_column_inner_bound CERT)
    (matrix_body_bound CERT) (matrix_outer_bound CERT) ZERO TWO INNER_TWO RUN)
    as [block [ARRAY [SCHEDULE EXIT]]].
  apply (checked_matrix_interchange_preserves_actual_memory (matrix_schedule_bound CERT)) in SCHEDULE.
  unfold clight_fragment_run; cbn; rewrite EXIT; apply matrix_target_encode with (block := block);
    try assumption; [exact (matrix_distinct_row_bound CERT)|exact (matrix_distinct_row_column CERT)|
    exact (matrix_distinct_bound_column CERT)|exact (matrix_distinct_row_inner_bound CERT)|
    exact (matrix_distinct_column_inner_bound CERT)].
Qed.

Definition readonly_matrix_rule source d (CERT : matrix_certificate source d) : readonly_clight_rule source.
Proof.
  rewrite (matrix_source_bound CERT).
  refine {| readonly_candidate := matrix_described_target d;
    readonly_guard := matrix_guard_tree (matrix_row d) (matrix_bound d) (matrix_inner_bound d);
    readonly_domain := readonly_matrix_domain d; readonly_premise := readonly_matrix_premise d |}.
  - intro temps; apply readonly_matrix_condition.
  - intro temps; apply quiet_forward_loop_equivalent.
    + intros entry [_ COMPLETE] _; exact COMPLETE.
    + apply described_matrix_target_quiet.
    + intros entry observed _ PREMISE RUN; exact (readonly_matrix_forward CERT PREMISE RUN).
  - intros temps p e le m le' m' RUN; split.
    + exact (@matrix_source_guard_domain (adapter_entry temps) (Clight.globalenv p) e le m
        (described_array d) (matrix_row d) (matrix_bound d) (matrix_column d) (matrix_inner_bound d)
        (matrix_inner_body d) (matrix_outer_body d) le' m'
        (matrix_distinct_row_column CERT) (matrix_distinct_bound_column CERT) (matrix_distinct_column_inner_bound CERT)
        (matrix_body_bound CERT) (matrix_outer_bound CERT) RUN).
    + exact (@quiet_source_completion_from_run (matrix_described_source d) (adapter_entry temps)
        (Entry (Clight.globalenv p) e le m) (FragmentObservation E0 le' m' Out_normal)
        (described_matrix_source_quiet CERT) RUN).
Defined.

Definition choose_readonly_matrix source : option (readonly_clight_rule source) :=
  match propose_matrix_description source with
  | Some d => match check_matrix_description source d with
    | Some CERT => Some (readonly_matrix_rule CERT)
    | None => None end
  | None => None end.

Definition compile_readonly_matrix := compile_readonly_rewrites choose_readonly_matrix structured_progress_supported.

Theorem compile_readonly_matrix_correct p target :
  compile_readonly_matrix p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_rewrites_correct, structured_progress_supported_sound. Qed.

Print Assumptions readonly_matrix_condition.
Print Assumptions readonly_matrix_forward.
Print Assumptions readonly_matrix_rule.
Print Assumptions compile_readonly_matrix_correct.
