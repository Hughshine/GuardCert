From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop ClightNoWrap ClightTempFrame
  ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryAffineInnerPointerSyntax
  GuardMemoryAffineInnerPointerSourceDomain.
From GuardInterface Require Import GuardedRewrite ReadonlyConditionComposition ClightConditionComposition
  ClightReadonlyRewrite ClightObservedHeaderPrefix ClightAffinePreparedState
  ClightAffineDomainFacts ClightAffineSnapshotRows ClightAffineSnapshotSourceInputs ClightAffineSnapshotPreparation
  ClightAffineSnapshotSyntax ClightAffineSnapshotReachedCondition ClightFirstReachedWidth
  ClightAffineSnapshotTransport ClightAffineZeroSnapshotRows ClightAffineZeroSnapshotPrefix
  ClightAffineZeroSnapshotTransport ClightAffineZeroSnapshotScan ClightAffineZeroSnapshotReady.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section CHECKED.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let source:=snapshot_cached_source site.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let cache:=affine_inner_pointer_bound shape.
Let root:=snapshot_root site.
Let child:=snapshot_child site.
Let child_cache:=snapshot_child_cache site.
Let header:=snapshot_original_header site.
Let expression:=affine_inner_pointer_expression package.
Let cap:=affine_inner_pointer_column_limit package.
Variable skip : nat.
Variable bounds : list MemoryNested.A.interval.
Variable tree : decision_tree.
Hypothesis COMPILE : compile_first_reached_width 0 cap skip row
  (memory_affine_inner_pointer_header shape expression)bounds expression=Some tree.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Let H:=readonly_clight_host fe observe.
Let D:=snapshot_first_reached_domain site bounds fe.
Let prepared:=affine_zero_preparation_tree site tree.
Let scan:=@affine_zero_snapshot_scan_tree source package root child child_cache header
  (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
  (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe.
Let preservation:=affine_snapshot_point_preservation package root child child_cache.
Definition affine_zero_checked_snapshot_tree:=decision_bind prepared scan(Decision false).
Definition affine_zero_checked_snapshot_facts entry:=affine_domain_ready package entry /\ preservation entry.

Definition affine_zero_checked_snapshot_condition :
  readonly_condition H D affine_zero_checked_snapshot_facts affine_zero_checked_snapshot_tree.
Proof.
  apply(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
    D(affine_domain_ready package)preservation prepared scan).
  - exact(@affine_zero_preparation_condition original site skip bounds tree COMPILE fe O observe).
  - eapply readonly_condition_restrict.
    + exact(@affine_zero_snapshot_scan_condition source package root child child_cache header
        (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
        (snapshot_header_word site)(snapshot_cached_body_exact site)fe O observe).
    + intros entry[DOMAIN READY]; exact(conj(proj1 DOMAIN)READY).
Defined.

(** Exact transport of the given original execution. Source completion is
    recovered from the source premise; the guard never executes its stores. *)
Theorem affine_zero_checked_snapshot_source_execution entry after final :
  D entry -> decision_run entry affine_zero_checked_snapshot_tree true ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    original E0 after final Out_normal ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (frontend_counted_loop row cache(affine_inner_pointer_outer_body shape))E0 after final Out_normal.
Proof.
  intros DOMAIN RUN SOURCE.
  destruct(readonly_sound affine_zero_checked_snapshot_condition entry true entry DOMAIN(conj RUN eq_refl))
    as [_ SOUND].
  destruct(SOUND eq_refl)as [READY PRESERVES].
  pose proof(@affine_zero_snapshot_prepared_entry source package root child child_cache header
    (snapshot_root_protected site)(snapshot_child_protected site)fe entry(proj1 DOMAIN)READY)as PREPARED.
  destruct(@affine_snapshot_initial_words source package root child child_cache header fe entry(proj1 DOMAIN))
    as [ROW CACHE].
  assert(CAP:signed_range(affine_inner_pointer_row_limit package)).
  { pose proof(affine_inner_pointer_control_limits(affine_inner_pointer_syntax package))as CAPS;
      inversion CAPS; subst; tauto. }
  destruct(@memory_affine_inner_pointer_header_sound shape(affine_inner_pointer_row_limit package)entry
    CAP ROW CACHE(affine_domain_ready_header READY))as [ZERO REST].
  assert(INV:@affine_zero_snapshot_execution_invariant source package root child child_cache entry
    (affine_prepared_count package entry)(entry_temps entry)(entry_memory entry)).
  { exists 0; split; [pose proof(affine_domain_count_range READY); lia|split; [exact ZERO|split]].
    - apply temp_agree_refl.
    - unfold affine_snapshot_observations,header_observations_match; apply Forall_app; split;
        apply cached_signed_initial_observations; [exact(proj1(proj2 PREPARED))|exact(proj2(proj2 PREPARED))]. }
  rewrite(snapshot_source_exact site)in SOURCE.
  exact(proj1(@affine_zero_snapshot_loaded_to_cached source package root child child_cache header
    (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
    (snapshot_header_word site)(snapshot_cached_body_exact site)fe entry PREPARED PRESERVES
    (entry_temps entry)(entry_memory entry)E0 after final Out_normal INV SOURCE)).
Qed.
End CHECKED.

Print Assumptions affine_zero_checked_snapshot_condition.
Print Assumptions affine_zero_checked_snapshot_source_execution.
