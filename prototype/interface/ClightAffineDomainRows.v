From GuardInterface Require Import ClightAffineDomainFacts.
From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame ClightPureExpr
  ClightLoopSyntax ClightRegionProgress ClightStraightLine ClightFrontendLoopProtocol ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryRanges
  GuardMemoryRecursiveSource GuardMemoryScalarPointerBody GuardMemorySourceParameters
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext
  GuardMemoryParametricSourceClight GuardMemoryParametricFirstBody GuardMemoryAffinePointerBody
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerRegionSource
  GuardMemoryMultiPointerSequence GuardMemoryPointerSequence GuardMemoryLoadedExternalTransport GuardMemoryParametricGuard.
From GuardInterface Require Import ClightAffineInnerPointerSourceGuard ClightAffinePreparedState ClightAffinePreparedRows ClightAffineDomainFacts.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section ROWS.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let cache := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let expression := affine_inner_pointer_expression package.
Let geometry := memory_source_other_parameters row cache expression++affine_inner_pointer_body_parameters package.
Let scalars := affine_inner_pointer_scalars package.
Let CERT := affine_inner_pointer_syntax package.

Variable pointer : ident.
Hypothesis FRESH : pointer <> row /\ pointer <> column /\ pointer <> inner_bound.
Let PROTECTED:=@affine_prepared_external_protected source package pointer FRESH.

(** This decoder consumes the actual checked source package and prepared
    entry. There is no client-supplied row-correspondence hypothesis. *)
Theorem affine_domain_actual_row_decode_exact fe entry i current before after final :
  affine_domain_ready package entry -> 0 <= i < affine_prepared_count package entry ->
  current ! row = Some (Vint (Int.repr i)) ->
  temp_agree (affine_prepared_stable package pointer) (entry_temps entry) current ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current before
    (affine_inner_pointer_outer_body shape) E0 after final Out_normal ->
  counted_iterations (affine_prepared_point package entry i) (Z.to_nat (affine_prepared_upper package entry i))
    0 before final /\ after = memory_parametric_settle column inner_bound
      (affine_prepared_upper package entry) i current.
Proof.
  intros READY I ROW FRAME RUN.
  set (N := affine_prepared_count package entry).
  set (rows := Z.to_nat N).
  set (geometry_values := map (affine_prepared_valuation entry) geometry).
  set (scalar_values := map (affine_prepared_valuation entry) scalars).
  pose proof (affine_domain_count_range READY) as COUNT.
  assert (RZ : Z.of_nat rows = N) by (unfold rows; apply Z2Nat.id; lia).
  assert (GEOMETRY : memory_source_parameter_values (affine_inner_pointer_geometry package) entry =
    N::geometry_values) by reflexivity.
  assert (SCALARS : memory_source_parameter_values scalars entry = scalar_values) by reflexivity.
  assert (CONTEXT : memory_source_parameter_values (memory_affine_inner_pointer_region_context package) entry =
    (N::geometry_values)++scalar_values).
  { unfold memory_affine_inner_pointer_region_context,memory_source_parameter_values; rewrite map_app; reflexivity. }
  assert (PARAMETERS : memory_nest_bindings (cache::geometry) (Z.of_nat rows::geometry_values) (entry_temps entry)).
  { rewrite RZ; change (memory_nest_bindings (cache::geometry)
      (map (affine_prepared_valuation entry) (cache::geometry)) (entry_temps entry)).
    apply memory_scalar_register_bindings; intros identifier MEMBER.
    exists (Int.repr (affine_prepared_valuation entry identifier)); apply (@affine_domain_words source package entry READY identifier).
    unfold memory_affine_inner_pointer_region_context; apply in_or_app; left; exact MEMBER. }
  assert (SCALAR_WORDS : memory_nest_bindings scalars scalar_values (entry_temps entry)).
  { apply memory_scalar_register_bindings; intros identifier MEMBER.
    exists (Int.repr (affine_prepared_valuation entry identifier)); apply (@affine_domain_words source package entry READY identifier).
    unfold memory_affine_inner_pointer_region_context; apply in_or_app; right; exact MEMBER. }
  assert (INNER : forall k, 0 <= k < Z.of_nat rows ->
    (0 <= L.eval_expr (k::(Z.of_nat rows::geometry_values)++scalar_values) (affine_inner_pointer_encoded package)
      <= affine_inner_pointer_column_limit package) /\
    signed_range (L.eval_expr (k::(Z.of_nat rows::geometry_values)++scalar_values) (affine_inner_pointer_encoded package))).
  { intros k K; rewrite RZ in K; rewrite RZ,<-CONTEXT;
      apply affine_domain_upper_range; [exact READY|exact K]. }
  assert (VALUE : forall k temps memory, 0 <= k < Z.of_nat rows ->
    temps ! row = Some (Vint (Int.repr k)) ->
    temp_agree (affine_prepared_stable package pointer) (entry_temps entry) temps ->
    eval_expr (entry_ge entry) (entry_env entry) temps memory (memory_source_affine_code expression)
      (Vint (Int.repr (L.eval_expr (k::(Z.of_nat rows::geometry_values)++scalar_values) (affine_inner_pointer_encoded package))))).
  { intros k temps memory K ROW_K FRAME_K; rewrite RZ,<-CONTEXT; apply affine_domain_upper_value;
      [exact READY|exact ROW_K|].
    eapply temp_agree_weaken; [|exact FRAME_K]; intros identifier MEMBER; right; exact MEMBER. }
  destruct (@memory_affine_pointer_external_row_decode fe (entry_ge entry) (entry_env entry)
    row cache column inner_bound pointer (memory_source_affine_code expression) (affine_inner_pointer_encoded package)
    (affine_inner_pointer_body shape) (affine_inner_pointer_outer_body shape) geometry scalars
    (affine_inner_pointer_pointers package) (affine_inner_pointer_geometry_caps package)
    (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_extent package) (affine_inner_pointer_operations package)
    (affine_inner_pointer_rc CERT) (affine_inner_pointer_rn CERT) (affine_inner_pointer_nc CERT)
    (affine_inner_pointer_rk CERT) (affine_inner_pointer_nk CERT) (affine_inner_pointer_ck CERT)
    PROTECTED (affine_inner_pointer_unique CERT)
    (affine_inner_pointer_operations_valid CERT) (affine_inner_pointer_operations_covered CERT)
    (affine_inner_pointer_body_exact CERT) (affine_inner_pointer_outer_exact CERT)
    rows geometry_values scalar_values (entry_temps entry)
    ltac:(intro EMPTY; rewrite EMPTY in RZ; cbn in RZ; lia)
    ltac:(rewrite RZ; exact (proj2 COUNT)) INNER
    ltac:(rewrite RZ,<-GEOMETRY; exact (affine_domain_ready_ranges READY))
    PARAMETERS SCALAR_WORDS (memory_source_affine_pure expression) VALUE i current before after final
    ltac:(rewrite RZ; exact I) ROW FRAME RUN) as [ITER EXIT].
  rewrite RZ in ITER,EXIT; rewrite <-CONTEXT in ITER,EXIT; rewrite <-GEOMETRY,<-SCALARS in ITER.
  split; assumption.
Qed.

Theorem affine_domain_actual_row_decode fe entry i current before after final :
  affine_domain_ready package entry -> 0 <= i < affine_prepared_count package entry ->
  current ! row = Some (Vint (Int.repr i)) ->
  temp_agree (affine_prepared_stable package pointer) (entry_temps entry) current ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current before
    (affine_inner_pointer_outer_body shape) E0 after final Out_normal ->
  counted_iterations (affine_prepared_point package entry i) (Z.to_nat (affine_prepared_upper package entry i))
    0 before final /\ after ! row = current ! row /\
    temp_agree (affine_prepared_stable package pointer) current after.
Proof.
  intros READY I ROW FRAME RUN.
  destruct (affine_domain_actual_row_decode_exact READY I ROW FRAME RUN) as [ITER EXIT].
  split; [exact ITER|rewrite EXIT; split].
  - pose proof (affine_inner_pointer_rc CERT) as RC; change (row <> column) in RC.
    pose proof (affine_inner_pointer_rk CERT) as RK; change (row <> inner_bound) in RK.
    unfold memory_parametric_settle; rewrite !PTree.gso by congruence; reflexivity.
  - unfold memory_parametric_settle; eapply temp_agree_trans; apply temp_agree_set.
    + intro MEMBER; exact (proj2 (proj2 (PROTECTED MEMBER)) eq_refl).
    + intro MEMBER; exact (proj1 (proj2 (PROTECTED MEMBER)) eq_refl).
Qed.
End ROWS.

Print Assumptions affine_domain_actual_row_decode_exact.
Print Assumptions affine_domain_actual_row_decode.
