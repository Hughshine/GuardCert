From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame
  ClightLoopSyntax ClightRegionProgress ClightFrontendLoopProtocol CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffinePointerLoadedDomain GuardMemoryAffineRowSeparation GuardMemoryAffineWriteSeparation
  GuardMemoryObservationStability GuardMemoryParametricSourceClight GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import ClightPreloadSnapshot ClightLoadedBoundSyntax ClightAffineLoadedBoundTransport
  ClightAffineInnerPointerSourceGuard ClightAffinePreparedState ClightAffinePreparedRows ClightAffineLoadedStability.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section CACHE.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable pointer : ident.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let cache := affine_inner_pointer_bound shape.
Let CERT := affine_inner_pointer_syntax package.
Hypothesis FRESH : pointer <> row /\ pointer <> column /\ pointer <> inner_bound.

Lemma affine_dynamic_loaded_cache_member : In cache (affine_prepared_stable package pointer).
Proof.
  right; unfold affine_prepared_body_stable; apply in_or_app; right.
  unfold memory_affine_inner_pointer_region_context; apply in_or_app; left; cbn; auto.
Qed.

(** The accepted guard supplies physical separation for actual source
    points. The language bridge then replaces repeated bound reads with
    the retained snapshot without changing memory or public registers. *)
Theorem affine_dynamic_loaded_cache_execution fe entry after final :
  loaded_preload_domain row cache pointer (affine_inner_pointer_pointers package) entry ->
  affine_inner_pointer_ready package entry -> affine_loaded_writes_separated package pointer entry ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (memory_affine_pointer_loaded_source package pointer) E0 after final Out_normal ->
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    source E0 after final Out_normal.
Proof.
  intros [ROW_DOMAIN [SNAPSHOT OBSERVED]] READY APART SOURCE.
  destruct SNAPSHOT as [word [block [offset [CACHE [POINTER READ]]]]].
  change ((entry_temps entry) ! cache = Some (Vint word)) in CACHE.
  set (N := affine_prepared_count package entry).
  assert (RANGE : 0 < N <= Int.max_signed).
  { pose proof (affine_prepared_count_range READY) as COUNT.
    pose proof (Int.signed_range (temp_word cache (entry_temps entry))) as SIGNED.
    change (Int.min_signed <= N <= Int.max_signed) in SIGNED; unfold N; lia. }
  assert (CACHE_N : (entry_temps entry) ! cache = Some (Vint (Int.repr N))).
  { apply (@affine_prepared_words source package entry READY cache).
    unfold memory_affine_inner_pointer_region_context; apply in_or_app; left; cbn; auto. }
  assert (READ_N : Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) = Some (Vint (Int.repr N)))
    by congruence.
  assert (CAP : signed_range (affine_inner_pointer_row_limit package)).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  destruct (@memory_affine_inner_pointer_header_sound shape (affine_inner_pointer_row_limit package) entry CAP
    ROW_DOMAIN (affine_prepared_cache_domain READY) (affine_inner_pointer_ready_header READY)) as [ZERO HEADER].
  assert (COLUMN_FRESH : ~ In column (affine_prepared_stable package pointer)).
  { intro MEMBER; exact (proj1 (proj2 (@affine_prepared_external_protected source package pointer FRESH column MEMBER)) eq_refl). }
  assert (INNER_FRESH : ~ In inner_bound (affine_prepared_stable package pointer)).
  { intro MEMBER; exact (proj2 (proj2 (@affine_prepared_external_protected source package pointer FRESH inner_bound MEMBER)) eq_refl). }
  assert (ROW_FRESH : ~ In row (affine_prepared_stable package pointer)).
  { intro MEMBER; exact (proj1 (@affine_prepared_external_protected source package pointer FRESH row MEMBER) eq_refl). }
  assert (WIDTH : forall i, 0 <= i < N -> 0 <= affine_prepared_upper package entry i).
  { intros i I; pose proof (affine_prepared_upper_range READY I); lia. }
  assert (DECODE : forall i current before exit last,
    0 <= i < N -> current ! row = Some (Vint (Int.repr i)) ->
    temp_agree (affine_prepared_stable package pointer) (entry_temps entry) current ->
    exec_stmt fe (entry_ge entry) (entry_env entry) current before (affine_inner_pointer_outer_body shape)
      E0 exit last Out_normal ->
    counted_iterations (affine_prepared_point package entry i) (Z.to_nat (affine_prepared_upper package entry i))
      0 before last /\ exit = memory_parametric_settle column inner_bound (affine_prepared_upper package entry) i current).
  { intros i current before exit last I ROW FRAME RUN.
    eapply (@affine_prepared_actual_row_decode_exact source package pointer FRESH fe entry i current before exit last);
      eassumption. }
  assert (POINT : forall i j before last, 0 <= i < N -> 0 <= j < affine_prepared_upper package entry i ->
    affine_prepared_point package entry i j before last ->
    location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) last =
    location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) before).
  { intros i j before last I J STEP; eapply memory_pointer_sequence_observation_preserved; [|exact STEP].
    apply (APART i I j J); exact POINTER. }
  rewrite (affine_inner_pointer_source_exact CERT).
  apply (proj1 (@affine_loaded_bound_cached fe (entry_ge entry) (entry_env entry) row cache pointer column inner_bound
    (affine_inner_pointer_outer_body shape) (affine_prepared_point package entry) (affine_prepared_upper package entry)
    (affine_prepared_stable package pointer) (entry_temps entry) block offset N RANGE
    (affine_inner_pointer_rc CERT) (affine_inner_pointer_rk CERT) COLUMN_FRESH INNER_FRESH ROW_FRESH
    affine_dynamic_loaded_cache_member ltac:(left; reflexivity) CACHE_N POINTER
    (@affine_prepared_outer_quiet source package) (@affine_prepared_outer_normal source package)
    WIDTH DECODE POINT (entry_temps entry) (entry_memory entry) E0 after final Out_normal
    ltac:(exists 0; split; [lia|split; [exact ZERO|split; [apply temp_agree_refl|exact READ_N]]]) SOURCE)).
Qed.

Theorem affine_dynamic_loaded_cached_domain fe entry :
  memory_affine_pointer_loaded_completed package pointer fe entry -> affine_inner_pointer_ready package entry ->
  affine_loaded_writes_separated package pointer entry -> affine_inner_pointer_observed_completed package fe entry.
Proof.
  intros [DOMAIN [after [final SOURCE]]] READY APART; split.
  - exists after,final; rewrite <- (affine_inner_pointer_source_exact CERT).
    eapply affine_dynamic_loaded_cache_execution; eassumption.
  - exact (proj2 (proj2 DOMAIN)).
Qed.
End CACHE.

Print Assumptions affine_dynamic_loaded_cache_execution.
Print Assumptions affine_dynamic_loaded_cached_domain.
