From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame
  ClightLoopSyntax ClightRegionProgress ClightFrontendLoopProtocol CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerRegionSource
  GuardMemoryAffineInnerPointerSourceDomain GuardMemoryParametricGuard GuardMemoryObservationStability.
From GuardInterface Require Import ClightDependentBoundSyntax ClightDependentHeaderObservations
  ClightObservedHeaderPrefix ClightObservedHeaderCache ClightAffineInnerPointerSourceGuard
  ClightAffinePreparedState ClightAffineDependentLoadedPrefix ClightAffineDependentLoadedStability
  ClightAffinePreparedRows.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section CACHE.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root pointer_cache : ident.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let cache := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let CERT := affine_inner_pointer_syntax package.
Hypothesis ROOT_FRESH : root <> row /\ root <> column /\ root <> inner_bound.
Hypothesis POINTER_FRESH : pointer_cache <> row /\ pointer_cache <> column /\ pointer_cache <> inner_bound.

Lemma affine_dependent_cache_member : In cache (affine_dependent_stable package root pointer_cache).
Proof.
  right; right; unfold affine_prepared_body_stable; apply in_or_app; right.
  unfold memory_affine_inner_pointer_region_context; apply in_or_app; left; cbn; auto.
Qed.

(** Every callback comes from the checked package and accepted full scan.
    The original composite header remains the source and refusal branch. *)
Theorem affine_dependent_cache_execution fe entry after final :
  affine_dependent_loaded_completed package root pointer_cache fe entry -> affine_inner_pointer_ready package entry ->
  affine_dependent_writes_separated package root pointer_cache entry ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (affine_dependent_loaded_source package root) E0 after final Out_normal ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    source E0 after final Out_normal.
Proof.
  intros [ROW_DOMAIN [CACHED [OBSERVED COMPLETED]]] READY APART SOURCE.
  set (N := affine_prepared_count package entry).
  assert (RANGE : 0 <= N <= Int.max_signed).
  { pose proof (affine_prepared_count_range READY) as COUNT.
    pose proof (Int.signed_range (temp_word cache (entry_temps entry))) as SIGNED.
    change (Int.min_signed <= N <= Int.max_signed) in SIGNED; unfold N; lia. }
  assert (CACHE_N : (entry_temps entry) ! cache = Some (Vint (Int.repr N))).
  { apply (@affine_prepared_words source package entry READY cache).
    unfold memory_affine_inner_pointer_region_context; apply in_or_app; left; cbn; auto. }
  assert (CAP : signed_range (affine_inner_pointer_row_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  destruct (@memory_affine_inner_pointer_header_sound shape (affine_inner_pointer_row_limit package) entry CAP
    ROW_DOMAIN (affine_prepared_cache_domain READY) (affine_inner_pointer_ready_header READY)) as [ZERO HEADER].
  rewrite (affine_inner_pointer_source_exact CERT).
  apply (proj1 (@observed_header_cached_execution fe (entry_ge entry) (entry_env entry) row cache
    (dependent_bound_test row root) (affine_inner_pointer_outer_body shape)
    (affine_dependent_stable package root pointer_cache) (entry_temps entry)
    (dependent_header_observations root pointer_cache cache entry) N RANGE affine_dependent_cache_member
    (@affine_dependent_fresh_row source package root pointer_cache ROOT_FRESH POINTER_FRESH) CACHE_N
    (@affine_prepared_outer_quiet source package) (@affine_prepared_outer_normal source package)
    (affine_prepared_upper package entry) (affine_prepared_point package entry)
    ltac:(intros i I; pose proof (affine_prepared_upper_range READY I); lia)
    ltac:(intros i current memory I ROW FRAME READS;
      apply (@affine_dependent_actual_header source package root pointer_cache entry i current memory);
      [split; assumption|exact I|exact ROW|exact FRAME|exact READS])
    ltac:(intros i current memory exit last I ROW FRAME BODY;
      apply (@affine_dependent_actual_row_decode source package root pointer_cache ROOT_FRESH POINTER_FRESH fe
        entry i current memory exit last); [split; assumption|exact I|exact ROW|exact FRAME|exact BODY])
    ltac:(intros observation MEMBER i j first last I J STEP;
      eapply memory_pointer_sequence_observation_preserved;
      [apply (APART i I j J observation MEMBER)|exact STEP])
    (entry_temps entry) (entry_memory entry) E0 after final Out_normal
    ltac:(exists 0; split; [lia|split; [exact ZERO|split; [apply temp_agree_refl|]]];
      apply dependent_header_initial_observations; exact CACHED) SOURCE)).
Qed.

Theorem affine_dependent_cached_domain fe entry :
  affine_dependent_loaded_completed package root pointer_cache fe entry -> affine_inner_pointer_ready package entry ->
  affine_dependent_writes_separated package root pointer_cache entry -> affine_inner_pointer_observed_completed package fe entry.
Proof.
  intros DOMAIN READY APART; pose proof DOMAIN as ORIGINAL; split.
  - destruct DOMAIN as [ROW [CACHED [OBSERVED [after [final SOURCE]]]]]; exists after,final.
    rewrite <- (affine_inner_pointer_source_exact CERT).
    eapply affine_dependent_cache_execution; eassumption.
  - exact (proj1 (proj2 (proj2 DOMAIN))).
Qed.
End CACHE.

Print Assumptions affine_dependent_cache_member.
Print Assumptions affine_dependent_cache_execution.
Print Assumptions affine_dependent_cached_domain.
