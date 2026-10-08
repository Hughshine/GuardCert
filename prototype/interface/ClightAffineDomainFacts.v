From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightNoWrap ClightCountedLoop
  ClightTempFrame ClightPureExpr ClightLoopSyntax ClightRegionProgress ClightStraightLine
  ClightRedundantSet ClightRectangularGuard ClightFrontendLoopProtocol ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryNaryCompute GuardMemoryNaryRanges
  GuardMemoryRecursiveSource GuardMemoryScalarPointerBody GuardMemorySourceParameters
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext
  GuardMemoryAffineSourceLoop GuardMemoryParametricGuard GuardMemoryParametricSourceDomain
  GuardMemoryParametricSourceClight GuardMemoryParametricFirstBody GuardMemoryAffinePointerBody
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryZeroWidthPointerSource GuardMemoryMultiPointerSequence
  GuardMemoryPointerSequence GuardMemoryLoadedExternalTransport GuardMemoryAffineAddressSpecialization.
From GuardInterface Require Import ClightAffineInnerPointerSourceGuard ClightAffinePreparedState.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Nonnegative affine model facts. Input typing must already have been
    produced from licensed source observations; this record licenses no read. *)
Record affine_domain_ready source (package:memory_affine_inner_pointer_package source) entry : Prop := {
  affine_domain_ready_header : memory_affine_inner_pointer_header_accept (affine_inner_pointer_shape package)
    (affine_inner_pointer_row_limit package) entry=true;
  affine_domain_ready_width : memory_affine_inner_pointer_zero_width_property (affine_inner_pointer_shape package)
    (affine_inner_pointer_expression package) (affine_inner_pointer_column_limit package) entry;
  affine_domain_ready_ranges : memory_nary_ranges (affine_inner_pointer_geometry_caps package)
    (memory_source_parameter_values (affine_inner_pointer_geometry package) entry);
  affine_domain_ready_view : MemoryNested.A.typed_view (memory_affine_inner_pointer_region_context package)
    (memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry) (entry_temps entry)
}.

Section STATE.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let cache := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let expression := affine_inner_pointer_expression package.
Let parameters := affine_inner_pointer_geometry package.
Let context := memory_affine_inner_pointer_region_context package.
Let CERT := affine_inner_pointer_syntax package.

Lemma affine_domain_words entry : affine_domain_ready package entry ->
  forall identifier, In identifier context ->
    (entry_temps entry) ! identifier = Some (Vint (Int.repr (affine_prepared_valuation entry identifier))).
Proof.
  intros READY identifier MEMBER.
  destruct (@memory_source_typed_word _ _ _ identifier (affine_domain_ready_view READY) MEMBER) as [word LOOK].
  unfold affine_prepared_valuation,temp_word; rewrite LOOK,Int.repr_signed; reflexivity.
Qed.

Lemma affine_domain_cache_domain entry : affine_domain_ready package entry -> register_domain cache entry.
Proof.
  intro READY; eexists; apply affine_domain_words; [exact READY|].
  unfold context,memory_affine_inner_pointer_region_context,memory_affine_inner_pointer_parameters,
    memory_affine_inner_pointer_header,memory_source_context; apply in_or_app; left; cbn; auto.
Qed.

Lemma affine_domain_count_range entry : affine_domain_ready package entry ->
  0 < affine_prepared_count package entry <= affine_inner_pointer_row_limit package.
Proof.
  intro READY; pose proof (affine_domain_ready_header READY) as HEADER.
  unfold memory_affine_inner_pointer_header_accept in HEADER; apply andb_true_iff in HEADER as [_ RANGE].
  assert (CAP : signed_range (affine_inner_pointer_row_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  exact (proj2 (@register_range_sound cache (affine_inner_pointer_row_limit package) entry CAP
    (affine_domain_cache_domain READY) RANGE)).
Qed.

Lemma affine_domain_upper_range entry i : affine_domain_ready package entry ->
  0 <= i < affine_prepared_count package entry ->
  (0 <= affine_prepared_upper package entry i <= affine_inner_pointer_column_limit package) /\
    signed_range (affine_prepared_upper package entry i).
Proof.
  intros READY I; rewrite affine_prepared_upper_math.
  pose proof (affine_domain_ready_width READY) as WIDTH.
  unfold memory_affine_inner_pointer_zero_width_property in WIDTH.
  assert (RANGE : 0 <= memory_source_affine_math
    (memory_source_set_valuation (affine_prepared_valuation entry) row i) expression <= affine_inner_pointer_column_limit package).
  { unfold affine_prepared_valuation; rewrite <- memory_affine_inner_pointer_word_math.
    apply WIDTH; rewrite memory_source_word_temp; exact I. }
  assert (CAP : signed_range (affine_inner_pointer_column_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst;
    match goal with REST : Forall _ [_] |- _ => inversion REST; subst; tauto end. }
  split; [exact RANGE|unfold signed_range; split].
  - eapply Z.le_trans with (m:=0); [change (-2147483648<=0); lia|exact (proj1 RANGE)].
  - eapply Z.le_trans with (m:=affine_inner_pointer_column_limit package);
      [exact (proj2 RANGE)|exact (proj2 CAP)].
Qed.

Lemma affine_domain_upper_value entry i current memory : affine_domain_ready package entry ->
  current ! row = Some (Vint (Int.repr i)) ->
  temp_agree (affine_prepared_body_stable package) (entry_temps entry) current ->
  eval_expr (entry_ge entry) (entry_env entry) current memory (memory_source_affine_code expression)
    (Vint (Int.repr (affine_prepared_upper package entry i))).
Proof.
  intros READY ROW FRAME; rewrite affine_prepared_upper_math; apply memory_source_affine_iteration_value with
    (base:=entry_temps entry); [exact ROW| |].
  - intros identifier MEMBER; apply memory_source_affine_parameter_member in MEMBER as [READ OTHER].
    apply affine_domain_words; [exact READY|apply affine_prepared_header_read; assumption].
  - eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER;
      apply memory_source_affine_parameter_member in MEMBER as [READ OTHER].
    apply in_or_app; right; apply affine_prepared_header_read; assumption.
Qed.
End STATE.

Print Assumptions affine_domain_words.
Print Assumptions affine_domain_cache_domain.
Print Assumptions affine_domain_count_range.
Print Assumptions affine_domain_upper_range.
Print Assumptions affine_domain_upper_value.
