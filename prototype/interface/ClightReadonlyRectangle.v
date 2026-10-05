From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Events Errors Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep Csyntax Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightPureExpr
  ClightDecisionRule ClightNoWrap ClightRegionProgress ClightStructuredProgress ClightTempFrame
  ClightStraightLine ClightCountedLoop ClightFrontendLoopProtocol ClightLoopSyntax
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion
  ClightRectangularSelector.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyTreeSynthesis ClightQuietDeterminacy ClightLoopBridge ClightReadonlyCompiler.
Import ListNotations.
Set Implicit Arguments.

Definition readonly_rectangle_domain d entry :=
  rectangle_guard_domain (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d) entry /\
  quiet_source_completion (rectangle_described_source d) entry.
Definition readonly_rectangle_premise d :=
  rectangle_guard_property (described_shape d) (rectangle_row d) (rectangle_bound d)
    (rectangle_inner_bound d) tt.
Definition readonly_rectangle_tree source d (CERT : rectangle_certificate source d) :=
  synthesize_decision_tree (rectangle_guard_primitives (rectangle_row d) (rectangle_bound d)
    (rectangle_inner_bound d) (rectangle_layout_bound CERT)) (Fact tt).

Lemma described_rectangle_source_quiet source d (CERT : rectangle_certificate source d) :
  quiet_statement (rectangle_described_source d) = true.
Proof.
  assert (OUTER : quiet_statement (rectangle_described_outer_body d) = true).
  { apply flatten_quiet_certificate; rewrite (rectangle_outer_bound CERT).
    constructor; [reflexivity|constructor; [|constructor]].
    cbn [frontend_counted_loop quiet_statement counter_increment].
    rewrite (@rect_body_quiet (described_shape d) (described_array d) (rectangle_row d)
      (rectangle_column d) (rectangle_inner_body d) (rectangle_body_bound CERT)); reflexivity. }
  cbn [rectangle_described_source frontend_counted_loop quiet_statement counter_increment].
  rewrite OUTER; reflexivity.
Qed.

Lemma described_rectangle_source_normal source d (CERT : rectangle_certificate source d) :
  normal_statement (rectangle_described_source d) = true.
Proof.
  cbn [rectangle_described_source frontend_counted_loop normal_statement quiet_statement counter_increment].
  pose proof (described_rectangle_source_quiet CERT) as QUIET.
  cbn [rectangle_described_source frontend_counted_loop quiet_statement counter_increment] in QUIET.
  exact QUIET.
Qed.

Lemma described_rectangle_target_quiet d : quiet_statement (rectangle_described_target d) = true.
Proof. reflexivity. Qed.

Definition readonly_rectangle_condition fe source d (CERT : rectangle_certificate source d) :
  readonly_condition (readonly_clight_host fe (@eq fragment_observation))
    (readonly_rectangle_domain d) (readonly_rectangle_premise d) (readonly_rectangle_tree CERT).
Proof.
  unfold readonly_rectangle_tree, readonly_rectangle_premise.
  eapply readonly_condition_restrict; [|intros entry [DOMAIN COMPLETE]; exact DOMAIN].
  apply synthesized_scalar_tree_condition with
    (D := rectangle_guard_dimension (rectangle_row d) (rectangle_bound d)
      (rectangle_inner_bound d) (rectangle_layout_bound CERT)) (premise := Fact tt).
  - intros []; apply rectangle_guard_tree_pure.
  - intros []; constructor.
Defined.

Lemma readonly_rectangle_forward source d (CERT : rectangle_certificate source d) fe entry observed :
  readonly_rectangle_premise d entry ->
  clight_fragment_run fe (rectangle_described_source d) entry observed ->
  clight_fragment_run fe (rectangle_described_target d) entry observed.
Proof.
  destruct entry as [ge locals temps memory], observed as [trace after final out].
  intros [ZERO [[ND NR] [MD MR]]] RUN.
  pose proof (@quiet_execution_silent fe ge locals temps memory _ trace after final out
    RUN (described_rectangle_source_quiet CERT)) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals _ (described_rectangle_source_normal CERT)
    temps memory E0 after final out RUN) as NORMAL; subst out.
  destruct ND as [n NLOOK], MD as [m MLOOK].
  cbn [entry_temps] in NLOOK, MLOOK, ZERO, NR, MR.
  unfold temp_word in NR, MR; rewrite NLOOK in NR; rewrite MLOOK in MR.
  unfold clight_fragment_run; cbn; unfold rectangle_described_target, rectangle_described_source in *.
  eapply rectangle_local with (N := Int.signed n) (M := Int.signed m);
    try eassumption; try apply Int.signed_range;
    try (rewrite Int.repr_signed; assumption).
  all: try exact (rectangle_layout_bound CERT).
  all: try exact (rectangle_distinct_row_bound CERT).
  all: try exact (rectangle_distinct_row_column CERT).
  all: try exact (rectangle_distinct_bound_column CERT).
  all: try exact (rectangle_distinct_row_inner_bound CERT).
  all: try exact (rectangle_distinct_column_inner_bound CERT).
  all: try exact (rectangle_body_bound CERT).
  all: try exact (rectangle_outer_bound CERT).
Qed.

Definition readonly_rectangle_rule source d (CERT : rectangle_certificate source d) : readonly_clight_rule source.
Proof.
  rewrite (rectangle_source_bound CERT).
  refine {| readonly_candidate := rectangle_described_target d;
    readonly_guard := readonly_rectangle_tree CERT;
    readonly_domain := readonly_rectangle_domain d;
    readonly_premise := readonly_rectangle_premise d |}.
  - intro temps; apply readonly_rectangle_condition.
  - intro temps; apply quiet_forward_loop_equivalent.
    + intros entry [_ COMPLETE] _; exact COMPLETE.
    + apply described_rectangle_target_quiet.
    + intros entry observed _ PREMISE RUN; exact (readonly_rectangle_forward CERT PREMISE RUN).
  - intros temps p e le m le' m' RUN; split.
    + exact (@rectangle_source_guard_domain (described_shape d) (adapter_entry temps)
        (Clight.globalenv p) e le m (described_array d) (rectangle_row d) (rectangle_bound d)
        (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)
        (rectangle_described_outer_body d) le' m'
        (rectangle_distinct_row_bound CERT) (rectangle_distinct_row_column CERT)
        (rectangle_distinct_bound_column CERT) (rectangle_distinct_column_inner_bound CERT)
        (rectangle_body_bound CERT) (rectangle_outer_bound CERT) RUN).
    + exact (@quiet_source_completion_from_run (rectangle_described_source d) (adapter_entry temps)
        (Entry (Clight.globalenv p) e le m) (FragmentObservation E0 le' m' Out_normal)
        (described_rectangle_source_quiet CERT) RUN).
Defined.

Definition choose_readonly_rectangle source : option (readonly_clight_rule source) :=
  match propose_rectangle_description source with
  | Some d => match check_rectangle_description source d with
    | Some CERT => Some (readonly_rectangle_rule CERT)
    | None => None end
  | None => None end.

Definition compile_readonly_rectangle :=
  compile_readonly_rewrites choose_readonly_rectangle structured_progress_supported.

Theorem compile_readonly_rectangle_correct p target :
  compile_readonly_rectangle p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_rewrites_correct, structured_progress_supported_sound. Qed.

Print Assumptions readonly_rectangle_condition.
Print Assumptions readonly_rectangle_forward.
Print Assumptions readonly_rectangle_rule.
Print Assumptions compile_readonly_rectangle_correct.
