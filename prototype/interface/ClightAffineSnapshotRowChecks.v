From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightCountedLoop ClightTempFrame
  ClightRedundantSet ClightLoopSyntax CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryParametricGuard GuardMemoryAffineRowSeparation
  GuardMemoryAffineWriteSeparation GuardMemoryObservationStability GuardMemoryMultiPointerSequence.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition
  ClightConditionComposition ClightReadonlyRewrite ClightAffineSnapshotRows ClightAffineSnapshotPrefix
  ClightAffineSnapshotTransport ClightAffineInnerPointerSourceGuard ClightAffinePreparedState
  ClightAffinePreparedFootprints ClightObservedHeaderPrefix ClightObservedBodyPrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Reached original rows supply physical permissions for both probes. The
    arithmetic box alone does not license either pointer comparison. *)
Section ROWS.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root child child_cache : ident.
Variable header : expr.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let column := affine_inner_pointer_column shape.
Let cache := affine_inner_pointer_bound shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let cap := Z.to_nat(affine_inner_pointer_column_limit package).
Hypothesis ROOT_FRESH : root<>row /\ root<>column /\ root<>inner_bound.
Hypothesis CHILD_FRESH : child<>row /\ child<>column /\ child<>inner_bound.
Hypothesis CHILD_CACHE_MEMBER : In child_cache(affine_snapshot_stable package root child).
Hypothesis HEADER_WORD : ClightWordReadSnapshots.snapshot_word_expression header.
Hypothesis CACHED_BODY : affine_inner_pointer_outer_body shape=
  affine_snapshot_body package(ClightWordReadSnapshots.snapshot_word_replace
    (single_snapshot_binding child child_cache)header).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Let H := readonly_clight_host fe observe.
Let prefix := affine_snapshot_package_prefix package root child child_cache header fe.
Let D i entry := prefix i entry /\ i<affine_prepared_count package entry.
Let property pointer i entry := forall j,0<=j<affine_prepared_upper package entry i ->
  memory_affine_writes_separated(affine_prepared_point_values package entry i j)
    pointer(affine_inner_pointer_operations package)entry.
Definition affine_snapshot_row_property i entry := property root i entry /\ property child i entry.
Let probe pointer i := memory_affine_row_probe row column i(affine_inner_pointer_expression package)
  pointer(affine_inner_pointer_operations package)cap.
Definition affine_snapshot_row_probe i := decision_bind(probe root i)(probe child i)(Decision false).

Lemma affine_snapshot_column_cap : 0<Z.of_nat cap /\ Z.of_nat cap<=Int.max_signed.
Proof.
  pose proof(affine_inner_pointer_control_limits(affine_inner_pointer_syntax package))as CAPS.
  inversion CAPS; subst; match goal with REST:Forall _ [_] |- _ => inversion REST; subst;
    unfold cap,signed_range in *; rewrite Z2Nat.id by lia; lia end.
Qed.

Theorem affine_snapshot_row_domain pointer pointer_cache i entry :
  D i entry -> cached_signed_read pointer pointer_cache entry ->
  memory_affine_row_domain row column i(affine_inner_pointer_expression package)pointer
    (affine_inner_pointer_operations package)cap affine_prepared_valuation
    (fun entry j=>affine_prepared_point_values package entry i j)
    (fun entry=>affine_prepared_upper package entry i)entry.
Proof.
  intros [INV ACTIVE] READ.
  assert(READY:affine_inner_pointer_ready package entry)by(exact(proj1(proj1 INV))).
  assert(I:0<=i<affine_prepared_count package entry).
  { pose proof(proj1(proj2(proj2 INV)))as RANGE; change(0<=i<=affine_prepared_count package entry)in RANGE; lia. }
  unfold memory_affine_row_domain; split; [|split; [|split; [|split]]].
  - unfold cap; rewrite Z2Nat.id by(pose proof affine_snapshot_column_cap; unfold cap in *; lia).
    exact(proj1(affine_prepared_upper_range READY I)).
  - apply affine_prepared_upper_at_math.
  - intros identifier MEMBER ROW COLUMN; apply(@affine_prepared_words source package entry READY identifier).
    apply affine_prepared_header_read; assumption.
  - intros j J; apply affine_prepared_write_probes_ready; [exact READY|exact I|exact J|].
    exact(@affine_snapshot_prefix_write_receipts source package root child child_cache header
      ROOT_FRESH CHILD_FRESH CHILD_CACHE_MEMBER HEADER_WORD CACHED_BODY fe i entry INV ACTIVE j J).
  - destruct READ as [block [offset [word [POINTER [CACHE READ]]]]].
    exists block,offset,(Vint word); split; assumption.
Qed.

Definition affine_snapshot_single_row_condition pointer pointer_cache
  (RECEIPT:forall entry,affine_snapshot_ready package root child child_cache entry ->
    cached_signed_read pointer pointer_cache entry)i :
  readonly_condition H(D i)(property pointer i)(probe pointer i).
Proof.
  eapply readonly_condition_restrict.
  - exact(@memory_affine_row_separation_condition fe O observe row column pointer i
      (affine_inner_pointer_expression package)(affine_inner_pointer_operations package)cap
      affine_prepared_valuation(fun entry j=>affine_prepared_point_values package entry i j)
      (fun entry=>affine_prepared_upper package entry i)(proj2 affine_snapshot_column_cap)).
  - intros entry DOMAIN; eapply affine_snapshot_row_domain; [exact DOMAIN|apply RECEIPT].
    exact(proj1(proj1 DOMAIN)).
Defined.

Definition affine_snapshot_row_condition i :
  readonly_condition H(D i)(affine_snapshot_row_property i)(affine_snapshot_row_probe i).
Proof.
  apply(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
    (D i)(property root i)(property child i)(probe root i)(probe child i)).
  - exact(@affine_snapshot_single_row_condition root cache
      (fun entry READY=>proj1(proj2 READY))i).
  - eapply readonly_condition_restrict.
    + exact(@affine_snapshot_single_row_condition child child_cache
        (fun entry READY=>proj2(proj2 READY))i).
    + intros entry [DOMAIN ROOT]; exact DOMAIN.
Defined.

Lemma affine_snapshot_separated_observation pointer pointer_cache entry values before after observation :
  cached_signed_read pointer pointer_cache entry ->
  In observation(cached_signed_observations pointer pointer_cache entry) ->
  memory_affine_writes_separated values pointer(affine_inner_pointer_operations package)entry ->
  memory_multi_pointer_sequence_physical(entry_temps entry)values(affine_inner_pointer_operations package)before after ->
  location_load(fst observation)after=location_load(fst observation)before.
Proof.
  intros [block [offset [word [POINTER [CACHE READ]]]]] MEMBER APART STEP.
  unfold cached_signed_observations in MEMBER; rewrite POINTER,CACHE in MEMBER;
    cbn in MEMBER; destruct MEMBER as [SAME|[]]; subst observation.
  eapply memory_pointer_sequence_observation_preserved; [exact(APART _ _ POINTER)|exact STEP].
Qed.

Theorem affine_snapshot_row_condition_preserves i entry :
  D i entry -> affine_snapshot_row_property i entry ->
  forall observation, In observation(affine_snapshot_observations package root child child_cache entry) ->
  forall j before after,0<=j<affine_prepared_upper package entry i ->
  affine_prepared_point package entry i j before after ->
  location_load(fst observation)after=location_load(fst observation)before.
Proof.
  intros [INV ACTIVE] [ROOT CHILD] observation MEMBER j before after J STEP.
  pose proof(proj1 INV)as READY.
  unfold affine_snapshot_observations in MEMBER; apply in_app_or in MEMBER as [N|M].
  - eapply affine_snapshot_separated_observation; [exact(proj1(proj2 READY))|exact N|exact(ROOT j J)|exact STEP].
  - eapply affine_snapshot_separated_observation; [exact(proj2(proj2 READY))|exact M|exact(CHILD j J)|exact STEP].
Qed.
End ROWS.

Print Assumptions affine_snapshot_row_domain.
Print Assumptions affine_snapshot_single_row_condition.
Print Assumptions affine_snapshot_row_condition.
Print Assumptions affine_snapshot_row_condition_preserves.
