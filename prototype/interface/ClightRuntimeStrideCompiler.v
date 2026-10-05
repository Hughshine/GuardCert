From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Events Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard ClightGuard ClightDecisionRule ClightNoWrap ClightRedundantSet ClightCondition ClightRegionProgress ClightStructuredProgress
  ClightStraightLine ClightLoopSyntax ClightCountedLoop ClightFrontendLoopProtocol ClightFrontendRegion ClightRectangularStore ClightRectangularGuard
  ClightRectangularLoops ClightRectangularRegion ClightRectangularSelector ClightSyntaxEquality.
From GuardInterface Require Import GuardedRewrite ClightReadonlyTreeSynthesis ClightReadonlyRewrite ClightQuietDeterminacy ClightReadonlyCompiler
  ClightReadonlyLoopRule ClightRuntimeStrideBody ClightRuntimeStrideLoops
  ClightRuntimeStrideEntry ClightRuntimeStrideGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The description's shape records the static array extent and payload.
    Its stride field is only a layout-check placeholder. Generated addresses
    always read the runtime stride temporary, including in the candidate. *)
Record stride_description := StrideDescription {
  stride_rectangle : rectangle_description;
  stride_parameter : ident
}.
Definition stride_source d := rectangle_described_source (stride_rectangle d).
Definition stride_atom d := runtime_stride_store (described_shape (stride_rectangle d))
  (described_array (stride_rectangle d)) (rectangle_row (stride_rectangle d))
  (rectangle_column (stride_rectangle d)) (stride_parameter d).
Definition stride_target d := rectangle_interchanged (rectangle_row (stride_rectangle d))
  (rectangle_bound (stride_rectangle d)) (rectangle_column (stride_rectangle d))
  (rectangle_inner_bound (stride_rectangle d)) (stride_atom d).
Definition stride_domain d := runtime_stride_domain (rectangle_row (stride_rectangle d))
  (rectangle_bound (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d)) (stride_parameter d).
Definition stride_property d := stride_dimensions_property (rectangle_extent (described_shape (stride_rectangle d)))
  (rectangle_row (stride_rectangle d)) (rectangle_bound (stride_rectangle d))
  (rectangle_inner_bound (stride_rectangle d)) (stride_parameter d) tt.

Record stride_certificate source d := StrideCertificate {
  stride_source_bound : source = stride_source d;
  stride_body_bound : flatten_region (rectangle_inner_body (stride_rectangle d)) = [stride_atom d];
  stride_outer_bound : flatten_region (rectangle_described_outer_body (stride_rectangle d)) =
    [rectangle_reset (rectangle_column (stride_rectangle d));
     frontend_counted_loop (rectangle_column (stride_rectangle d))
       (rectangle_inner_bound (stride_rectangle d)) (rectangle_inner_body (stride_rectangle d))];
  stride_row_bound : rectangle_row (stride_rectangle d) <> rectangle_bound (stride_rectangle d);
  stride_row_column : rectangle_row (stride_rectangle d) <> rectangle_column (stride_rectangle d);
  stride_bound_column : rectangle_bound (stride_rectangle d) <> rectangle_column (stride_rectangle d);
  stride_row_inner_bound : rectangle_row (stride_rectangle d) <> rectangle_inner_bound (stride_rectangle d);
  stride_column_inner_bound : rectangle_column (stride_rectangle d) <> rectangle_inner_bound (stride_rectangle d);
  stride_parameter_row : stride_parameter d <> rectangle_row (stride_rectangle d);
  stride_parameter_column : stride_parameter d <> rectangle_column (stride_rectangle d);
  stride_static_layout : rectangle_layout_valid (described_shape (stride_rectangle d))
}.

Definition check_stride_description source d : option (stride_certificate source d).
Proof.
  destruct (statement_eq source (stride_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body (stride_rectangle d)))
    [stride_atom d]) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body (stride_rectangle d)))
    [rectangle_reset (rectangle_column (stride_rectangle d)); frontend_counted_loop
      (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))
      (rectangle_inner_body (stride_rectangle d))]) as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row (stride_rectangle d)) (rectangle_bound (stride_rectangle d))) as [|RN]; [exact None|].
  destruct (peq (rectangle_row (stride_rectangle d)) (rectangle_column (stride_rectangle d))) as [|RC]; [exact None|].
  destruct (peq (rectangle_bound (stride_rectangle d)) (rectangle_column (stride_rectangle d))) as [|NC]; [exact None|].
  destruct (peq (rectangle_row (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))) as [|RM]; [exact None|].
  destruct (peq (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))) as [|CM]; [exact None|].
  destruct (peq (stride_parameter d) (rectangle_row (stride_rectangle d))) as [|SR]; [exact None|].
  destruct (peq (stride_parameter d) (rectangle_column (stride_rectangle d))) as [|SC]; [exact None|].
  destruct (rectangle_layout_check (described_shape (stride_rectangle d))) eqn:LAYOUT; [|exact None].
  exact (Some (@StrideCertificate source d SOURCE BODY OUTER RN RC NC RM CM SR SC
    (@rectangle_layout_check_sound (described_shape (stride_rectangle d)) LAYOUT))).
Defined.

Definition propose_stride_description source : option stride_description :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset column _; inner_loop] => match propose_frontend_shape inner_loop with
      | Some (_,inner_bound,inner_body) => match flatten_region inner_body with
        | [Sassign (Ederef (Ebinop _ (Evar array (Tarray _ extent _))
            (Ebinop _ (Ebinop _ _ (Etempvar stride _) _) _ _) _) _)
            (Ebinop _ (Ebinop _ (Ebinop _ _ coefficient_expr _) _ _) bias_expr _)] =>
            match propose_rectangle_constant coefficient_expr, propose_rectangle_constant bias_expr with
            | Some coefficient, Some bias => Some (StrideDescription
                (RectangleDescription (RectangleShape extent 1 coefficient bias)
                  array row bound column inner_bound inner_body outer_body) stride)
            | _, _ => None end
        | _ => None end
      | None => None end
    | _ => None end
  | None => None end.

Lemma stride_source_quiet source d (CERT : stride_certificate source d) : quiet_statement (stride_source d) = true.
Proof.
  assert (OUTER : quiet_statement (rectangle_described_outer_body (stride_rectangle d)) = true).
  { apply flatten_quiet_certificate; rewrite (stride_outer_bound CERT).
    constructor; [reflexivity|constructor; [|constructor]].
    cbn [frontend_counted_loop quiet_statement counter_increment].
    rewrite (@runtime_body_quiet (described_shape (stride_rectangle d)) (described_array (stride_rectangle d))
      (rectangle_row (stride_rectangle d)) (rectangle_column (stride_rectangle d)) (stride_parameter d)
      (rectangle_inner_body (stride_rectangle d)) (stride_body_bound CERT)); reflexivity. }
  cbn [stride_source rectangle_described_source frontend_counted_loop quiet_statement counter_increment].
  rewrite OUTER; reflexivity.
Qed.
Lemma stride_source_normal source d (CERT : stride_certificate source d) : normal_statement (stride_source d) = true.
Proof. pose proof (stride_source_quiet CERT) as Q; exact Q. Qed.

Definition stride_guard source d (CERT : stride_certificate source d) :=
  synthesize_decision_tree (stride_dimensions_primitives (rectangle_row (stride_rectangle d))
    (rectangle_bound (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d)) (stride_parameter d)
    ltac:(pose proof (stride_static_layout CERT) as H; unfold rectangle_layout_valid in H;
      destruct H as [P [Q REST]]; exact (conj P Q))) (Fact tt).

Definition runtime_shape d word := RectangleShape (rectangle_extent (described_shape (stride_rectangle d)))
  (Int.signed word) (rectangle_coefficient (described_shape (stride_rectangle d)))
  (rectangle_bias (described_shape (stride_rectangle d))).
Lemma stride_runtime_layout source d (CERT : stride_certificate source d) word count :
  0 < Int.signed word -> 0 < count -> count * Int.signed word <= rectangle_extent (described_shape (stride_rectangle d)) ->
  rectangle_layout_valid (runtime_shape d word).
Proof.
  intros S N B; pose proof (stride_static_layout CERT) as STATIC.
  unfold runtime_shape, rectangle_layout_valid in *; cbn in *; nia.
Qed.

Theorem stride_forward source d (CERT : stride_certificate source d) fe entry observed :
  stride_domain d entry -> stride_property d entry ->
  clight_fragment_run fe (stride_source d) entry observed -> clight_fragment_run fe (stride_target d) entry observed.
Proof.
  destruct entry as [ge locals temps memory], observed as [trace after final out].
  intros [[I [N MD]] SD] [ZERO [NP [MP [SP [COL EXTENT]]]]] RUN.
  pose proof (@quiet_execution_silent fe ge locals temps memory _ trace after final out RUN (stride_source_quiet CERT)) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals _ (stride_source_normal CERT) temps memory E0 after final out RUN) as NORMAL; subst out.
  destruct N as [n NB].
  destruct (MD ZERO NP) as [m MB].
  destruct (SD ZERO NP MP) as [s SB].
  cbn [entry_temps] in *.
  unfold signed_entry_word, temp_word in NP, MP, SP, COL, EXTENT; cbn [entry_temps] in *.
  rewrite NB in NP, EXTENT; rewrite MB in MP, COL; rewrite SB in SP, COL, EXTENT.
  assert (VALID : rectangle_layout_valid (runtime_shape d s)) by
    (exact (@stride_runtime_layout source d CERT s (Int.signed n) SP NP EXTENT)).
  assert (LIMIT : 0 < Int.signed n <= rectangle_outer_limit (runtime_shape d s)).
  { unfold rectangle_outer_limit, runtime_shape; cbn; split; [exact NP|].
    apply Z.div_le_lower_bound; [exact SP|nia]. }
  assert (BODY : flatten_region (rectangle_inner_body (stride_rectangle d)) =
    [runtime_stride_store (runtime_shape d s) (described_array (stride_rectangle d))
      (rectangle_row (stride_rectangle d)) (rectangle_column (stride_rectangle d)) (stride_parameter d)]).
  { exact (stride_body_bound CERT). }
  unfold clight_fragment_run; cbn; unfold stride_source, rectangle_described_source in RUN.
  unfold stride_target, stride_atom.
  eapply runtime_stride_rectangle_forward with (d := runtime_shape d s) (N := Int.signed n) (M := Int.signed m);
    try exact RUN; try exact VALID; try exact BODY; try exact ZERO;
    try exact LIMIT; try (split; assumption); try apply Int.signed_range;
    try (cbn [runtime_shape]; rewrite Int.repr_signed; assumption).
  all: try exact (stride_row_bound CERT).
  all: try exact (stride_row_column CERT).
  all: try exact (stride_bound_column CERT).
  all: try exact (stride_row_inner_bound CERT).
  all: try exact (stride_column_inner_bound CERT).
  all: try exact (stride_parameter_row CERT).
  all: try exact (stride_parameter_column CERT).
  all: try exact (stride_outer_bound CERT).
  change (temps ! (stride_parameter d) = Some (Values.Vint (Int.repr (Int.signed s)))).
  rewrite Int.repr_signed; exact SB.
Qed.

Definition stride_rule source d (CERT : stride_certificate source d) : readonly_clight_rule source.
Proof.
  rewrite (stride_source_bound CERT).
  refine (@readonly_forward_loop_rule (stride_source d) (stride_target d) (stride_guard CERT)
    (stride_domain d) (stride_property d) (stride_source_quiet CERT) ltac:(reflexivity) _ _ _).
  - intro temps; apply stride_dimensions_condition.
  - intros temps entry observed DOMAIN PREMISE RUN; exact (stride_forward CERT DOMAIN PREMISE RUN).
  - intros temps p e le m le' m' RUN; unfold stride_domain.
    exact (@runtime_stride_domain_from_source (adapter_entry temps) (Clight.globalenv p) e
      (described_shape (stride_rectangle d)) (described_array (stride_rectangle d))
      (rectangle_row (stride_rectangle d)) (rectangle_bound (stride_rectangle d))
      (rectangle_column (stride_rectangle d)) (rectangle_inner_bound (stride_rectangle d))
      (stride_parameter d) (rectangle_inner_body (stride_rectangle d))
      (rectangle_described_outer_body (stride_rectangle d)) le m le' m'
      (stride_row_bound CERT) (stride_row_column CERT) (stride_bound_column CERT)
      (stride_column_inner_bound CERT) (stride_parameter_column CERT)
      (stride_body_bound CERT) (stride_outer_bound CERT) RUN).
Defined.
Definition choose_runtime_stride source : option (readonly_clight_rule source) :=
  match propose_stride_description source with
  | Some d => match check_stride_description source d with Some CERT => Some (stride_rule CERT) | None => None end
  | None => None end.
Definition compile_runtime_strides := compile_readonly_rewrites choose_runtime_stride structured_progress_supported.
Theorem compile_runtime_strides_correct p target : compile_runtime_strides p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_rewrites_correct, structured_progress_supported_sound. Qed.
Print Assumptions stride_runtime_layout.
Print Assumptions stride_forward.
Print Assumptions stride_rule.
Print Assumptions choose_runtime_stride.
Print Assumptions compile_runtime_strides_correct.
