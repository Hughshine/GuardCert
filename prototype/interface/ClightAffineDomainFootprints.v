From GuardInterface Require Import ClightAffineDomainFacts ClightAffineDomainRows.
From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCondition ClightCountedLoop.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryNaryRanges GuardMemoryMultiPointerCompute
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineSourceExpressions GuardMemoryAffineAddressSpecialization
  GuardMemoryAffineWriteSeparation GuardMemoryWriteReceipts GuardMemoryScalarPointerBody
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryParametricSourceDomain GuardMemoryParametricGuard.
From GuardInterface Require Import ClightAffineInnerPointerSourceGuard ClightAffinePreparedState ClightAffinePreparedFootprints ClightAffineDomainFacts.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section FOOTPRINTS.
Variable source : Clight.statement.
Variable package : memory_affine_inner_pointer_package source.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let column := affine_inner_pointer_column shape.
Let expression := affine_inner_pointer_expression package.
Let parameters := affine_inner_pointer_geometry package.
Let layout := memory_affine_inner_pointer_layout shape expression (affine_inner_pointer_body_parameters package).
Let scalars := affine_inner_pointer_scalars package.
Let CERT := affine_inner_pointer_syntax package.

Lemma affine_domain_point_ranges entry i j : affine_domain_ready package entry ->
  0 <= i < affine_prepared_count package entry -> 0 <= j < affine_prepared_upper package entry i ->
  memory_nary_ranges
    (memory_affine_inner_pointer_limits (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
      (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package))
    (map (memory_affine_at_value row column i j (affine_prepared_valuation entry)) layout).
Proof.
  intros READY I J; unfold layout,row,column,expression,shape.
  rewrite (@affine_prepared_layout_values source package entry i j).
  unfold memory_affine_inner_pointer_limits,memory_nary_ranges.
  pose proof (affine_domain_count_range READY) as COUNT.
  pose proof (affine_domain_upper_range READY I) as WIDTH.
  constructor; [lia|constructor; [lia|exact (affine_domain_ready_ranges READY)]].
Qed.

(** Existing checked arithmetic plus receipts from a reached physical row
    establish the probe's complete domain. Allocation is not inferred from a
    shape/range bound. No observation-stability premise is consumed here. *)
Theorem affine_domain_write_probes_ready entry i j : affine_domain_ready package entry ->
  0 <= i < affine_prepared_count package entry -> 0 <= j < affine_prepared_upper package entry i ->
  Forall (memory_write_receipt (entry_temps entry) (affine_prepared_point_values package entry i j)
    (entry_memory entry)) (affine_inner_pointer_operations package) ->
  Forall (memory_affine_write_ready row column i j (affine_prepared_valuation entry)
    (affine_prepared_point_values package entry i j) entry) (affine_inner_pointer_operations package).
Proof.
  intros READY I J RECEIPTS; apply Forall_forall; intros operation MEMBER.
  eapply memory_affine_checked_write_ready with
    (limits:=memory_affine_inner_pointer_limits (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
      (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package))
    (layout:=layout) (scalars:=scalars) (extent:=affine_inner_pointer_extent package).
  - eapply Forall_forall; [exact (affine_inner_pointer_operations_valid CERT)|exact MEMBER].
  - apply affine_domain_point_ranges; assumption.
  - apply affine_prepared_point_values_at.
  - intros identifier IN ROW COLUMN; unfold layout,memory_affine_inner_pointer_layout in IN.
    apply in_app_or in IN as [COORDINATE|PARAMETER].
    + cbn in COORDINATE; destruct COORDINATE as [<-|[<-|[]]]; contradiction.
    + apply (@affine_domain_words source package entry READY identifier).
      unfold memory_affine_inner_pointer_region_context; apply in_or_app; left; exact PARAMETER.
  - eapply Forall_forall; eassumption.
Qed.
End FOOTPRINTS.

Print Assumptions affine_domain_point_ranges.
Print Assumptions affine_domain_write_probes_ready.
