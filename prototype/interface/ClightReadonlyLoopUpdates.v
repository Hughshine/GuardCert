From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Events Errors Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep Csyntax Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightPureExpr
  ClightDecisionRule ClightNoWrap ClightRegionProgress ClightStructuredProgress ClightTempFrame
  ClightStraightLine ClightCountedLoop ClightFrontendLoopProtocol ClightLoopSyntax
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion
  ClightRectangularSelector ClightRectangularUpdate ClightRectangularUpdateRegion
  ClightRectangularUpdateSelector ClightRectangularRowUpdate ClightRectangularRowRegion
  ClightRectangularRowSelector.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyTreeSynthesis ClightQuietDeterminacy ClightLoopBridge ClightReadonlyCompiler
  ClightReadonlyLoopRule ClightReadonlyRectangle.
Import ListNotations.
Set Implicit Arguments.

(** The common check is an actual synthesized read-only tree. Both body
    instances separately bind the complete source AST and prove the loop
    execution theorem; they do not assert unrestricted memory independence. *)
Definition readonly_rectangle_layout_tree d (VALID : rectangle_layout_valid (described_shape d)) :=
  synthesize_decision_tree (rectangle_guard_primitives (rectangle_row d) (rectangle_bound d)
    (rectangle_inner_bound d) VALID) (Fact tt).

Definition readonly_rectangle_layout_condition fe d
  (VALID : rectangle_layout_valid (described_shape d)) :
  readonly_condition (readonly_clight_host fe (@eq fragment_observation))
    (rectangle_guard_domain (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d))
    (readonly_rectangle_premise d) (@readonly_rectangle_layout_tree d VALID).
Proof.
  unfold readonly_rectangle_layout_tree, readonly_rectangle_premise.
  apply synthesized_scalar_tree_condition with
    (D := rectangle_guard_dimension (rectangle_row d) (rectangle_bound d)
      (rectangle_inner_bound d) VALID) (premise := Fact tt).
  - intros []; apply rectangle_guard_tree_pure.
  - intros []; constructor.
Defined.

Lemma rectangle_source_quiet_from_body d :
  quiet_statement (rectangle_inner_body d) = true ->
  flatten_region (rectangle_described_outer_body d) =
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)] ->
  quiet_statement (rectangle_described_source d) = true.
Proof.
  intros BODY FLAT.
  assert (OUTER : quiet_statement (rectangle_described_outer_body d) = true).
  { apply flatten_quiet_certificate; rewrite FLAT.
    constructor; [reflexivity|constructor; [|constructor]].
    cbn [frontend_counted_loop quiet_statement counter_increment]; rewrite BODY; reflexivity. }
  cbn [rectangle_described_source frontend_counted_loop quiet_statement counter_increment].
  rewrite OUTER; reflexivity.
Qed.

Lemma rectangle_source_normal_from_quiet d :
  quiet_statement (rectangle_described_source d) = true ->
  normal_statement (rectangle_described_source d) = true.
Proof.
  cbn [rectangle_described_source frontend_counted_loop normal_statement quiet_statement counter_increment].
  auto.
Qed.

Lemma readonly_rectangle_update_source_quiet source d (CERT : rectangle_update_certificate source d) :
  quiet_statement (rectangle_described_source d) = true.
Proof.
  apply rectangle_source_quiet_from_body.
  - exact (@rect_update_body_quiet (described_shape d) (described_array d) (rectangle_row d)
      (rectangle_column d) (rectangle_inner_body d) (rectangle_update_body_bound CERT)).
  - exact (rectangle_update_outer_bound CERT).
Qed.

Theorem readonly_rectangle_update_forward source d (CERT : rectangle_update_certificate source d) fe entry observed :
  readonly_rectangle_premise d entry ->
  clight_fragment_run fe (rectangle_described_source d) entry observed ->
  clight_fragment_run fe (rectangle_update_described_target d) entry observed.
Proof.
  destruct entry as [ge locals temps memory], observed as [trace after final out].
  intros [ZERO [[ND NR] [MD MR]]] RUN.
  pose proof (@quiet_execution_silent fe ge locals temps memory _ trace after final out
    RUN (readonly_rectangle_update_source_quiet CERT)) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals _
    (@rectangle_source_normal_from_quiet d (readonly_rectangle_update_source_quiet CERT))
    temps memory E0 after final out RUN) as NORMAL; subst out.
  destruct ND as [n NLOOK], MD as [m MLOOK].
  cbn [entry_temps] in NLOOK, MLOOK, ZERO, NR, MR.
  unfold temp_word in NR, MR; rewrite NLOOK in NR; rewrite MLOOK in MR.
  unfold clight_fragment_run; cbn; unfold rectangle_update_described_target, rectangle_described_source in *.
  eapply rectangle_update_local with (N := Int.signed n) (M := Int.signed m);
    try eassumption; try apply Int.signed_range;
    try (rewrite Int.repr_signed; assumption).
  all: try exact (rectangle_update_layout_bound CERT).
  all: try exact (rectangle_update_distinct_row_bound CERT).
  all: try exact (rectangle_update_distinct_row_column CERT).
  all: try exact (rectangle_update_distinct_bound_column CERT).
  all: try exact (rectangle_update_distinct_row_inner_bound CERT).
  all: try exact (rectangle_update_distinct_column_inner_bound CERT).
  all: try exact (rectangle_update_body_bound CERT).
  all: try exact (rectangle_update_outer_bound CERT).
Qed.

Definition readonly_rectangle_update_rule source d (CERT : rectangle_update_certificate source d) :
  readonly_clight_rule source.
Proof.
  rewrite (rectangle_update_source_bound CERT).
  apply readonly_forward_loop_rule with
    (candidate := rectangle_update_described_target d)
    (guard := @readonly_rectangle_layout_tree d (rectangle_update_layout_bound CERT))
    (domain := rectangle_guard_domain (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d))
    (premise := readonly_rectangle_premise d).
  - exact (readonly_rectangle_update_source_quiet CERT).
  - reflexivity.
  - intro temps; apply readonly_rectangle_layout_condition.
  - intros temps entry observed _ PREMISE RUN; exact (readonly_rectangle_update_forward CERT PREMISE RUN).
  - intros temps p e le m le' m' RUN.
    exact (@rectangle_update_source_guard_domain (described_shape d) (adapter_entry temps)
      (Clight.globalenv p) e le m (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)
      (rectangle_described_outer_body d) le' m'
      (rectangle_update_distinct_row_bound CERT) (rectangle_update_distinct_row_column CERT)
      (rectangle_update_distinct_bound_column CERT) (rectangle_update_distinct_column_inner_bound CERT)
      (rectangle_update_body_bound CERT) (rectangle_update_outer_bound CERT) RUN).
Defined.

Definition choose_readonly_rectangle_update source : option (readonly_clight_rule source) :=
  match propose_rectangle_update_description source with
  | Some d => match check_rectangle_update_description source d with
    | Some CERT => Some (readonly_rectangle_update_rule CERT)
    | None => None end
  | None => None end.

Lemma readonly_rectangle_row_update_source_quiet source d (CERT : rectangle_row_update_certificate source d) :
  quiet_statement (rectangle_described_source d) = true.
Proof.
  apply rectangle_source_quiet_from_body.
  - exact (@rect_row_update_body_quiet (described_shape d) (described_array d) (rectangle_row d)
      (rectangle_column d) (rectangle_inner_body d) (rectangle_row_update_body_bound CERT)).
  - exact (rectangle_row_update_outer_bound CERT).
Qed.

Theorem readonly_rectangle_row_update_forward source d (CERT : rectangle_row_update_certificate source d) fe entry observed :
  readonly_rectangle_premise d entry ->
  clight_fragment_run fe (rectangle_described_source d) entry observed ->
  clight_fragment_run fe (rectangle_row_update_described_target d) entry observed.
Proof.
  destruct entry as [ge locals temps memory], observed as [trace after final out].
  intros [ZERO [[ND NR] [MD MR]]] RUN.
  pose proof (@quiet_execution_silent fe ge locals temps memory _ trace after final out
    RUN (readonly_rectangle_row_update_source_quiet CERT)) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals _
    (@rectangle_source_normal_from_quiet d (readonly_rectangle_row_update_source_quiet CERT))
    temps memory E0 after final out RUN) as NORMAL; subst out.
  destruct ND as [n NLOOK], MD as [m MLOOK].
  cbn [entry_temps] in NLOOK, MLOOK, ZERO, NR, MR.
  unfold temp_word in NR, MR; rewrite NLOOK in NR; rewrite MLOOK in MR.
  unfold clight_fragment_run; cbn; unfold rectangle_row_update_described_target, rectangle_described_source in *.
  eapply rectangle_row_update_local with (N := Int.signed n) (M := Int.signed m);
    try eassumption; try apply Int.signed_range;
    try (rewrite Int.repr_signed; assumption).
  all: try exact (rectangle_row_update_layout_bound CERT).
  all: try exact (rectangle_row_update_distinct_row_bound CERT).
  all: try exact (rectangle_row_update_distinct_row_column CERT).
  all: try exact (rectangle_row_update_distinct_bound_column CERT).
  all: try exact (rectangle_row_update_distinct_row_inner_bound CERT).
  all: try exact (rectangle_row_update_distinct_column_inner_bound CERT).
  all: try exact (rectangle_row_update_body_bound CERT).
  all: try exact (rectangle_row_update_outer_bound CERT).
Qed.

Definition readonly_rectangle_row_update_rule source d (CERT : rectangle_row_update_certificate source d) :
  readonly_clight_rule source.
Proof.
  rewrite (rectangle_row_update_source_bound CERT).
  apply readonly_forward_loop_rule with
    (candidate := rectangle_row_update_described_target d)
    (guard := @readonly_rectangle_layout_tree d (rectangle_row_update_layout_bound CERT))
    (domain := rectangle_guard_domain (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d))
    (premise := readonly_rectangle_premise d).
  - exact (readonly_rectangle_row_update_source_quiet CERT).
  - reflexivity.
  - intro temps; apply readonly_rectangle_layout_condition.
  - intros temps entry observed _ PREMISE RUN; exact (readonly_rectangle_row_update_forward CERT PREMISE RUN).
  - intros temps p e le m le' m' RUN.
    exact (@rectangle_row_update_source_guard_domain (described_shape d) (adapter_entry temps)
      (Clight.globalenv p) e le m (described_array d) (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)
      (rectangle_described_outer_body d) le' m'
      (rectangle_row_update_distinct_row_bound CERT) (rectangle_row_update_distinct_row_column CERT)
      (rectangle_row_update_distinct_bound_column CERT) (rectangle_row_update_distinct_column_inner_bound CERT)
      (rectangle_row_update_body_bound CERT) (rectangle_row_update_outer_bound CERT) RUN).
Defined.

Definition choose_readonly_rectangle_row_update source : option (readonly_clight_rule source) :=
  match propose_rectangle_row_update_description source with
  | Some d => match check_rectangle_row_update_description source d with
    | Some CERT => Some (readonly_rectangle_row_update_rule CERT)
    | None => None end
  | None => None end.

(** User selection remains outside the framework. This instance tries three
    checked body templates and uses the original source when none applies. *)
Definition choose_readonly_rectangles source : option (readonly_clight_rule source) :=
  match choose_readonly_rectangle source with
  | Some rule => Some rule
  | None => match choose_readonly_rectangle_update source with
    | Some rule => Some rule
    | None => choose_readonly_rectangle_row_update source end end.
Definition compile_readonly_rectangles :=
  compile_readonly_rewrites choose_readonly_rectangles structured_progress_supported.
Theorem compile_readonly_rectangles_correct p target :
  compile_readonly_rectangles p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_rewrites_correct, structured_progress_supported_sound. Qed.

Print Assumptions readonly_rectangle_layout_condition.
Print Assumptions readonly_rectangle_update_forward.
Print Assumptions readonly_rectangle_update_rule.
Print Assumptions readonly_rectangle_row_update_forward.
Print Assumptions readonly_rectangle_row_update_rule.
Print Assumptions compile_readonly_rectangles_correct.
