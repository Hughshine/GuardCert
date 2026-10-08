From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightNoWrap ClightRedundantSet
  ClightLoopSyntax ClightRegionProgress ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineInnerPointerSyntax
  GuardMemoryAffineSourceContext
  GuardMemoryAffineInnerPointerSourceDomain GuardMemoryAffineInnerPointerRegionSource
  GuardMemoryParametricSourceDomain GuardMemoryParametricGuard GuardMemoryMultiPointerSequence
  GuardMemoryWriteReceipts GuardMemoryParametricSourceClight GuardMemoryPointerSequence.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightWordReadSnapshots
  ClightAffineHeaderSnapshots ClightAffineSnapshotRows ClightAffineSnapshotSourceInputs ClightAffineSnapshotPreparation
  ClightObservedHeaderPrefix ClightObservedBodyPrefix ClightAffineInnerPointerSourceGuard
  ClightAffinePreparedState ClightAffinePreparedRows ClightStrictLoopProgress ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section PREFIX.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root child child_cache : ident.
Variable header : expr.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let cache := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let stable := affine_snapshot_stable package root child.
Let CERT := affine_inner_pointer_syntax package.
Hypothesis ROOT_FRESH : root<>row /\ root<>column /\ root<>inner_bound.
Hypothesis CHILD_FRESH : child<>row /\ child<>column /\ child<>inner_bound.
Hypothesis CHILD_CACHE_MEMBER : In child_cache stable.
Hypothesis HEADER_WORD : snapshot_word_expression header.
Hypothesis CACHED_BODY : affine_inner_pointer_outer_body shape=
  affine_snapshot_body package(snapshot_word_replace(single_snapshot_binding child child_cache)header).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.

Lemma affine_snapshot_root_cache_member : In cache stable.
Proof.
  unfold stable,affine_snapshot_stable,affine_prepared_stable; right; right.
  unfold affine_prepared_body_stable; apply in_or_app; right.
  unfold memory_affine_inner_pointer_region_context; apply in_or_app; left.
  unfold memory_affine_inner_pointer_parameters,memory_affine_inner_pointer_header,memory_source_context.
  left; reflexivity.
Qed.

Theorem affine_snapshot_actual_header entry i current memory :
  affine_snapshot_ready package root child child_cache entry ->
  0<=i<=affine_prepared_count package entry -> current!row=Some(Vint(Int.repr i)) ->
  temp_agree stable(entry_temps entry)current ->
  header_observations_match(affine_snapshot_observations package root child child_cache entry)memory ->
  expression_test(loaded_bound_test row root)(Entry(entry_ge entry)(entry_env entry)current memory)
    (i<?affine_prepared_count package entry).
Proof.
  intros [READY [ROOT CHILD]] RANGE ROW FRAME OBSERVED.
  unfold affine_snapshot_observations,header_observations_match in OBSERVED;
    apply Forall_app in OBSERVED as [ROOT_OBS CHILD_OBS].
  destruct(@cached_signed_current_read root cache stable entry current memory
    (or_intror(or_introl eq_refl))affine_snapshot_root_cache_member ROOT FRAME ROOT_OBS)
    as [word [CACHE READ]].
  assert(ENTRY_CACHE:(entry_temps entry)!cache=Some(Vint word)).
  { rewrite FRAME in CACHE by exact affine_snapshot_root_cache_member; exact CACHE. }
  unfold affine_prepared_count,affine_prepared_valuation in RANGE|-*; fold shape cache in RANGE|-*.
  unfold temp_word in RANGE|-*; rewrite ENTRY_CACHE in RANGE|-*.
  assert(SIGNED:signed_range i).
  { unfold signed_range; change(-2147483648<=i<=2147483647).
    pose proof(Int.signed_range word); change(-2147483648<=Int.signed word<=2147483647)in H; lia. }
  assert(FLAG:Int.lt(Int.repr i)word=(i<?Int.signed word)).
  { unfold Int.lt; rewrite Int.signed_repr by exact SIGNED.
    destruct(zlt i(Int.signed word)); [symmetry; apply Z.ltb_lt|symmetry; apply Z.ltb_ge]; lia. }
  rewrite <-FLAG; destruct(signed_load_inv READ)as [block [offset [POINTER LOAD]]].
  eapply loaded_bound_test_eval; [exact ROW|exact POINTER|exact LOAD].
Qed.

Lemma affine_snapshot_prepared_entry entry :
  affine_snapshot_original_domain package root child child_cache header fe entry ->
  affine_inner_pointer_ready package entry -> affine_snapshot_ready package root child child_cache entry.
Proof.
  intros DOMAIN READY; pose proof DOMAIN as ORIGINAL.
  destruct DOMAIN as [ROOT [CHILD SOURCE]].
  destruct(@affine_snapshot_initial_words source package root child child_cache header fe entry ORIGINAL)as [ROW CACHE].
  assert(CAP:signed_range(affine_inner_pointer_row_limit package)).
  { pose proof(affine_inner_pointer_control_limits CERT)as CAPS; inversion CAPS; subst; tauto. }
  destruct(@memory_affine_inner_pointer_header_sound shape(affine_inner_pointer_row_limit package)entry
    CAP ROW CACHE(affine_inner_pointer_ready_header READY))as [ZERO [_ POSITIVE]].
  split; [exact READY|split; [exact ROOT|]].
  apply CHILD; exact(@affine_snapshot_zero_active source package entry CACHE ZERO(proj1 POSITIVE)).
Qed.

Theorem affine_snapshot_prefix_initial entry :
  affine_snapshot_original_domain package root child child_cache header fe entry ->
  affine_inner_pointer_ready package entry -> affine_snapshot_package_prefix package root child child_cache header fe 0 entry.
Proof.
  intros DOMAIN READY; pose proof(affine_snapshot_prepared_entry DOMAIN READY)as PREPARED.
  destruct DOMAIN as [ROOT [CHILD [after [final SOURCE]]]].
  assert(CAP:signed_range(affine_inner_pointer_row_limit package)).
  { pose proof(affine_inner_pointer_control_limits CERT)as CAPS; inversion CAPS; subst; tauto. }
  destruct(@affine_snapshot_initial_words source package root child child_cache header fe entry
    ltac:(split; [exact ROOT|split; [exact CHILD|exists after,final; exact SOURCE]]))as [ROW CACHE].
  destruct(@memory_affine_inner_pointer_header_sound shape(affine_inner_pointer_row_limit package)entry
    CAP ROW CACHE(affine_inner_pointer_ready_header READY))as [ZERO RANGE].
  eapply(@observed_body_prefix_initial fe row cache(loaded_bound_test row root)
    (affine_snapshot_body package header)stable(affine_snapshot_ready package root child child_cache)
    (affine_snapshot_observations package root child child_cache)entry after final).
  - exact PREPARED.
  - exact(affine_prepared_cache_domain READY).
  - pose proof(affine_prepared_count_range READY); change(0<=affine_prepared_count package entry); lia.
  - exact ZERO.
  - unfold affine_snapshot_observations,header_observations_match; apply Forall_app; split;
      apply cached_signed_initial_observations; [exact ROOT|exact(proj2(proj2 PREPARED))].
  - exact SOURCE.
Qed.

(** A concrete consumer of the stronger body-prefix decoder. These physical
    write permissions come from reached original rows, not a rectangular box. *)
Theorem affine_snapshot_prefix_write_receipts i entry :
  affine_snapshot_package_prefix package root child child_cache header fe i entry ->
  i<affine_prepared_count package entry -> forall j,0<=j<affine_prepared_upper package entry i ->
  Forall(memory_write_receipt(entry_temps entry)(affine_prepared_point_values package entry i j)(entry_memory entry))
    (affine_inner_pointer_operations package).
Proof.
  intros INV ACTIVE j J.
  assert(READY:affine_inner_pointer_ready package entry)by(exact(proj1(proj1 INV))).
  assert(I:0<=i<affine_prepared_count package entry).
  { pose proof(proj1(proj2(proj2 INV)))as RANGE; change(0<=i<=affine_prepared_count package entry)in RANGE; lia. }
  pose proof(@observed_body_prefix_receipt fe row cache(loaded_bound_test row root)
    (affine_snapshot_body package header)stable(affine_snapshot_ready package root child child_cache)
    (affine_snapshot_observations package root child child_cache)(affine_prepared_upper package)(affine_prepared_point package)
    (@affine_setup_child_normal column inner_bound header(affine_inner_pointer_body shape)
      (@memory_pointer_sequence_quiet(affine_inner_pointer_operations package)(affine_inner_pointer_body shape)
        (affine_inner_pointer_body_exact CERT)))
    (@affine_setup_child_quiet column inner_bound header(affine_inner_pointer_body shape)
      (@memory_pointer_sequence_quiet(affine_inner_pointer_operations package)(affine_inner_pointer_body shape)
        (affine_inner_pointer_body_exact CERT)))
    affine_snapshot_actual_header
    (@affine_snapshot_actual_row_decode source package root child child_cache header ROOT_FRESH CHILD_FRESH
      CHILD_CACHE_MEMBER HEADER_WORD CACHED_BODY fe)i entry INV ACTIVE)as RECEIPT.
  destruct RECEIPT as [current [before [after [final [ROW [FRAME [READS [BACK [BODY ITER]]]]]]]]].
  pose proof(@counted_pointer_sequence_write_receipts(entry_temps entry)
    (fun j=>affine_prepared_point_values package entry i j)(affine_inner_pointer_operations package)
    (Z.to_nat(affine_prepared_upper package entry i))0 before final ITER j
    ltac:(rewrite Z2Nat.id by(pose proof(affine_prepared_upper_range READY I); lia); lia))as WRITES.
  eapply Forall_impl; [|exact WRITES]; intros operation WRITE;
    eapply memory_write_receipt_back; [exact BACK|exact WRITE].
Qed.
End PREFIX.

Print Assumptions affine_snapshot_actual_header.
Print Assumptions affine_snapshot_prepared_entry.
Print Assumptions affine_snapshot_prefix_initial.
Print Assumptions affine_snapshot_prefix_write_receipts.
