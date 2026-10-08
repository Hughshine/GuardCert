From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import ClightAffineDomainFacts ClightAffinePreparedState
  ClightAffineSnapshotRows ClightAffineSnapshotTransport ClightAffineZeroSnapshotRows
  ClightAffineZeroSnapshotReady ClightObservedHeaderPrefix ClightAffineSnapshotSyntax
  ClightZeroRmwObservation ClightAffineLoadedBoundTransport.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The caller supplies observations already matching the reached row entry.
    This law concerns actual row execution, not arbitrary physical point
    memories, and makes no assertion of complete memory equality. *)
Definition affine_snapshot_row_observation_preservation source
    (package:memory_affine_inner_pointer_package source) root child child_cache header fe entry :=
  forall i before memory after final,
    0<=i<affine_prepared_count package entry ->
    before!(affine_inner_pointer_row(affine_inner_pointer_shape package))=Some(Vint(Int.repr i)) ->
    temp_agree(affine_snapshot_stable package root child)(entry_temps entry)before ->
    header_observations_match(affine_snapshot_observations package root child child_cache entry)memory ->
    exec_stmt fe(entry_ge entry)(entry_env entry)before memory(affine_snapshot_body package header)
      E0 after final Out_normal ->
    header_observations_match(affine_snapshot_observations package root child child_cache entry)final.

Lemma cached_signed_words_preserved pointer cache entry before after :
  mint32_words_preserved before after ->
  header_observations_match(cached_signed_observations pointer cache entry)before ->
  header_observations_match(cached_signed_observations pointer cache entry)after.
Proof.
  unfold cached_signed_observations.
  destruct((entry_temps entry)!pointer)as [pointer_value|]; try destruct pointer_value;
    destruct((entry_temps entry)!cache)as [cache_value|]; try destruct cache_value;
    cbn [header_observations_match]; intros WORDS OBSERVED; try solve[constructor].
  unfold header_observations_match in OBSERVED|-*; rewrite Forall_forall in OBSERVED|-*.
  intros observation MEMBER; cbn in MEMBER; destruct MEMBER as [<-|[]].
  cbn [fst snd location_load]; apply WORDS.
  pose proof(OBSERVED _ (or_introl eq_refl))as LOAD; exact LOAD.
Qed.

Lemma affine_snapshot_words_preserved source(package:memory_affine_inner_pointer_package source)
    root child child_cache entry before after :
  mint32_words_preserved before after ->
  header_observations_match(affine_snapshot_observations package root child child_cache entry)before ->
  header_observations_match(affine_snapshot_observations package root child child_cache entry)after.
Proof.
  intros WORDS OBSERVED; unfold affine_snapshot_observations,header_observations_match in *.
  apply Forall_app in OBSERVED as [ROOT CHILD]; apply Forall_app; split;
    eapply cached_signed_words_preserved; eassumption.
Qed.

(** Ordinary checked source data selects the service. The scalar membership
    also lets the numeric preparation produce its definedness automatically. *)
Record affine_snapshot_rmw_site original(site:affine_snapshot_source_package original) := {
  affine_snapshot_rmw_alpha : ident;
  affine_snapshot_rmw_context : In affine_snapshot_rmw_alpha
    (memory_affine_inner_pointer_region_context(snapshot_cached_package site));
  affine_snapshot_rmw_checked : check_zero_rmw_control affine_snapshot_rmw_alpha
    (affine_snapshot_body(snapshot_cached_package site)(snapshot_original_header site))=true
}.

Theorem affine_snapshot_zero_rmw_row_preservation original(site:affine_snapshot_source_package original)
    (rmw:affine_snapshot_rmw_site site) fe entry :
  (entry_temps entry)!(affine_snapshot_rmw_alpha rmw)=Some(Vint Int.zero) ->
  affine_snapshot_row_observation_preservation(snapshot_cached_package site)(snapshot_root site)
    (snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)fe entry.
Proof.
  intros ZERO i before memory after final RANGE ROW FRAME READS RUN.
  eapply affine_snapshot_words_preserved; [|exact READS].
  exact(proj1(@checked_zero_rmw_control_execution(affine_snapshot_rmw_alpha rmw)
    fe(entry_ge entry)(entry_env entry)before memory
    (affine_snapshot_body(snapshot_cached_package site)(snapshot_original_header site))
    E0 after final Out_normal RUN(affine_snapshot_rmw_checked rmw)
    ltac:(rewrite FRAME; [exact ZERO|unfold affine_snapshot_stable,affine_prepared_stable,
      affine_prepared_body_stable; right; right; apply in_or_app; right;
      exact(affine_snapshot_rmw_context rmw)]))).
Qed.

Theorem affine_snapshot_separated_row_preservation original(site:affine_snapshot_source_package original)
    fe entry :
  affine_zero_snapshot_ready(snapshot_cached_package site)(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)entry ->
  affine_snapshot_point_preservation(snapshot_cached_package site)(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)entry ->
  affine_snapshot_row_observation_preservation(snapshot_cached_package site)(snapshot_root site)
    (snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)fe entry.
Proof.
  intros READY PRESERVES i before memory after final RANGE ROW FRAME READS RUN.
  destruct(@affine_zero_snapshot_actual_row_decode(snapshot_cached_source site)(snapshot_cached_package site)
    (snapshot_root site)(snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
    (snapshot_root_protected site)(snapshot_child_protected site)(snapshot_cache_member site)
    (snapshot_header_word site)(snapshot_cached_body_exact site)fe entry i before memory after final
    READY RANGE ROW FRAME READS RUN)as [ITER EXIT].
  unfold header_observations_match in READS|-*; rewrite Forall_forall in READS|-*.
  intros observation MEMBER.
  assert(SAME:location_load(fst observation)final=location_load(fst observation)memory).
  { eapply counted_observation_preserved; [|exact ITER].
    intros j JR first last STEP; eapply PRESERVES; [exact RANGE| |exact STEP|exact MEMBER].
    rewrite Z2Nat.id in JR by(pose proof(affine_domain_upper_range(proj1 READY)RANGE); lia); lia. }
  rewrite SAME; exact(READS observation MEMBER).
Qed.

Print Assumptions cached_signed_words_preserved.
Print Assumptions affine_snapshot_words_preserved.
Print Assumptions affine_snapshot_zero_rmw_row_preservation.
Print Assumptions affine_snapshot_separated_row_preservation.
