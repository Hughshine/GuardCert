From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightNoWrap ClightCountedLoop
  ClightLoopSyntax ClightRegionProgress ClightFrontendLoopProtocol CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryPointerSequence GuardMemoryWriteReceipts.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyPrefixScan
  ClightReadonlyRewrite ClightConditionComposition ClightReadonlyBranching ClightLoadedBoundSyntax
  ClightAffineHeaderSnapshots ClightWordReadSnapshots ClightAffineSnapshotRows ClightAffineSnapshotPrefix
  ClightAffineSnapshotSourceInputs ClightAffineSnapshotTransport ClightAffineSnapshotRowChecks
  ClightAffineInnerPointerSourceGuard ClightAffinePreparedState ClightAffinePreparedRows
  ClightObservedHeaderPrefix ClightObservedBodyPrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A finite actual readonly tree: accept this row before licensing the next.
    A refused row skips all later row probes. No original stores are executed
    by the guard; its prefix cursor records source reachability in the proof. *)
Section SCAN.
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
Let ready := affine_snapshot_ready package root child child_cache.
Let observations := affine_snapshot_observations package root child child_cache.
Let body := affine_snapshot_body package header.
Let prefix := affine_snapshot_package_prefix package root child child_cache header.
Hypothesis ROOT_FRESH : root<>row /\ root<>column /\ root<>inner_bound.
Hypothesis CHILD_FRESH : child<>row /\ child<>column /\ child<>inner_bound.
Hypothesis CHILD_CACHE_MEMBER : In child_cache stable.
Hypothesis HEADER_WORD : snapshot_word_expression header.
Hypothesis CACHED_BODY : affine_inner_pointer_outer_body shape=
  affine_snapshot_body package(snapshot_word_replace(single_snapshot_binding child child_cache)header).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Let H := readonly_clight_host fe observe.
Let row_probe := affine_snapshot_row_probe package root child.
Let row_property := affine_snapshot_row_property package root child.
Let CERT := affine_inner_pointer_syntax package.
Let LEAF_QUIET := @memory_pointer_sequence_quiet _ _(affine_inner_pointer_body_exact CERT).

Definition affine_snapshot_scan_spec : readonly_prefix_spec H Z.
Proof.
  refine(@observed_body_prefix_spec fe row cache(loaded_bound_test row root)body stable ready observations
    (affine_prepared_upper package)(affine_prepared_point package)
    _ _ _ _ _ _ _ O observe row_probe row_property _ _).
  - intros [SAME|MEMBER].
    + change(child=row)in SAME; exact(proj1 CHILD_FRESH SAME).
    + exact(proj1(@affine_prepared_external_protected source package root ROOT_FRESH row MEMBER)eq_refl).
  - exact(@affine_setup_child_normal column inner_bound header(affine_inner_pointer_body shape)LEAF_QUIET).
  - exact(@affine_setup_child_quiet column inner_bound header(affine_inner_pointer_body shape)LEAF_QUIET).
  - exact(@affine_snapshot_actual_header source package root child child_cache ROOT_FRESH CHILD_FRESH).
  - exact(@affine_snapshot_actual_row_decode source package root child child_cache header
      ROOT_FRESH CHILD_FRESH CHILD_CACHE_MEMBER HEADER_WORD CACHED_BODY fe).
  - intros entry i READY RANGE; exact(proj1(proj1(affine_prepared_upper_range(proj1 READY)RANGE))).
  - intros entry i j before after STEP; eapply memory_pointer_sequence_accesses_back; exact STEP.
  - exact(@affine_snapshot_row_condition source package root child child_cache header
      ROOT_FRESH CHILD_FRESH CHILD_CACHE_MEMBER HEADER_WORD CACHED_BODY fe O observe).
  - intros i entry INV ACTIVE PROPERTY.
    exact(@affine_snapshot_row_condition_preserves source package root child child_cache header fe
      i entry(conj INV ACTIVE)PROPERTY).
Defined.

Definition affine_snapshot_scan_tree := synthesize_prefix_scan(clight_readonly_check_algebra fe observe)
  (clight_readonly_branch_algebra fe observe)affine_snapshot_scan_spec
  (Z.to_nat(affine_inner_pointer_row_limit package))0.

Lemma affine_snapshot_scan_rows fuel start entry :
  prefix_scan_property affine_snapshot_scan_spec fuel start entry ->
  forall i,start<=i<start+Z.of_nat fuel -> i<affine_prepared_count package entry -> row_property i entry.
Proof.
  revert start; induction fuel as [|fuel IH]; intros start PROP i RANGE ACTIVE; [cbn in RANGE; lia|].
  change(start<affine_prepared_count package entry -> row_property start entry /\
    prefix_scan_property affine_snapshot_scan_spec fuel(start+1)entry)in PROP.
  destruct(PROP ltac:(lia))as [PROPERTY REST]; destruct(Z.eq_dec i start); [subst; exact PROPERTY|].
  eapply IH; [exact REST|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
Qed.

Lemma affine_snapshot_scan_property_sound entry : ready entry ->
  prefix_scan_property affine_snapshot_scan_spec(Z.to_nat(affine_inner_pointer_row_limit package))0 entry ->
  affine_snapshot_point_preservation package root child child_cache entry.
Proof.
  intros READY PROP i j before after I J STEP observation MEMBER.
  assert(ROW_PROPERTY:row_property i entry).
  { eapply affine_snapshot_scan_rows; [exact PROP| |lia].
    rewrite Z2Nat.id by(pose proof(affine_prepared_count_range(proj1 READY)); lia).
    pose proof(affine_prepared_count_range(proj1 READY)); lia. }
  destruct ROW_PROPERTY as [ROOT CHILD].
  unfold affine_snapshot_observations in MEMBER; apply in_app_or in MEMBER as [N|M].
  - eapply affine_snapshot_separated_observation; [exact(proj1(proj2 READY))|exact N|exact(ROOT j J)|exact STEP].
  - eapply affine_snapshot_separated_observation; [exact(proj2(proj2 READY))|exact M|exact(CHILD j J)|exact STEP].
Qed.

Let D entry := affine_snapshot_original_domain package root child child_cache header fe entry /\
  affine_inner_pointer_ready package entry.

Definition affine_snapshot_scan_condition : readonly_condition H D
  (affine_snapshot_point_preservation package root child child_cache)affine_snapshot_scan_tree.
Proof.
  eapply readonly_condition_entails.
  - eapply readonly_condition_restrict.
    + exact(@synthesized_prefix_scan_condition clight_entry H Z(clight_readonly_check_algebra fe observe)
        (clight_readonly_branch_algebra fe observe)affine_snapshot_scan_spec
        (Z.to_nat(affine_inner_pointer_row_limit package))0).
    + intros entry [DOMAIN READY]; exact(@affine_snapshot_prefix_initial source package
        root child child_cache header ROOT_FRESH CHILD_FRESH fe entry DOMAIN READY).
  - intros entry [DOMAIN READY] PROP; apply affine_snapshot_scan_property_sound; [|exact PROP].
    exact(@affine_snapshot_prepared_entry source package root child child_cache header
      ROOT_FRESH CHILD_FRESH fe entry DOMAIN READY).
Defined.

Theorem affine_snapshot_scan_accepted_cached_source entry :
  D entry -> decision_run entry affine_snapshot_scan_tree true ->
  exists after final,
    exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      (affine_snapshot_source package root header)E0 after final Out_normal /\
    exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      (frontend_counted_loop row cache(affine_inner_pointer_outer_body shape))E0 after final Out_normal.
Proof.
  intros [DOMAIN READY] RUN.
  pose proof(readonly_sound affine_snapshot_scan_condition entry true entry(conj DOMAIN READY)(conj RUN eq_refl))
    as [_ SOUND].
  exact(@affine_snapshot_original_cached_completion source package root child child_cache header
    ROOT_FRESH CHILD_FRESH CHILD_CACHE_MEMBER HEADER_WORD CACHED_BODY fe entry
    (@affine_snapshot_prepared_entry source package root child child_cache header
      ROOT_FRESH CHILD_FRESH fe entry DOMAIN READY)
    (SOUND eq_refl)DOMAIN).
Qed.
End SCAN.

Print Assumptions affine_snapshot_scan_spec.
Print Assumptions affine_snapshot_scan_rows.
Print Assumptions affine_snapshot_scan_property_sound.
Print Assumptions affine_snapshot_scan_condition.
Print Assumptions affine_snapshot_scan_accepted_cached_source.
