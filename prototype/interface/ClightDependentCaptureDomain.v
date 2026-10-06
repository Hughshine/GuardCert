From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightLoopSyntax ClightStraightLine.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightDependentBoundSyntax ClightDependentHeaderObservations
  ClightAffineDependentLoadedPrefix ClightSourceObservation ClightPrivateScan ClightLoadedBoundSyntax.
Import ListNotations.
Set Implicit Arguments.

Definition dependent_guard_prefix loads root pointer_cache cache :=
  Ssequence (source_load_prefix loads) (dependent_header_capture root pointer_cache cache).
Lemma dependent_guard_prefix_supported loads root pointer_cache cache :
  private_scan_statement (dependent_guard_prefix loads root pointer_cache cache).
Proof.
  unfold dependent_guard_prefix,dependent_header_capture; apply scan_sequence;
    [apply source_load_prefix_supported|apply scan_sequence; apply scan_set].
Qed.
Lemma dependent_capture_writes root pointer_cache cache :
  writes_only [pointer_cache;cache] (dependent_header_capture root pointer_cache cache).
Proof. unfold dependent_header_capture; apply writes_sequence; constructor; cbn; auto. Qed.

(** Captured values are typed by the actual original header reached after the
    preparation, including its zero-trip case. No future read is assumed. *)
Theorem dependent_capture_header_receipt fe ge locals temps memory root pointer_cache cache captured row flag :
  pointer_cache <> root -> cache <> root -> cache <> pointer_cache ->
  exec_stmt fe ge locals temps memory (dependent_header_capture root pointer_cache cache) E0 captured memory Out_normal ->
  expression_test (dependent_bound_test row root) (Entry ge locals captured memory) flag ->
  dependent_cached_header root pointer_cache cache (Entry ge locals captured memory).
Proof.
  intros POINTER_ROOT CACHE_ROOT DISTINCT CAPTURE HEADER.
  unfold dependent_header_capture in CAPTURE; inversion CAPTURE; subst; [|contradiction].
  all: match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst; clear SET end.
  all: match goal with SET : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion SET; subst; clear SET end.
  match goal with LOAD : eval_expr _ _ _ _ (dependent_pointer_load _) _ |- _ =>
    apply dependent_pointer_load_inv in LOAD; destruct LOAD as [block [offset [ROOT READ_POINTER]]] end.
  match goal with LOAD : eval_expr _ _ _ _ (signed_load _) _ |- _ =>
    apply signed_load_inv in LOAD; destruct LOAD as [target [address [POINTER READ_BOUND]]] end.
  rewrite PTree.gss in POINTER; injection POINTER as VALUE; subst.
  destruct (dependent_bound_test_facts HEADER) as [counter [bound [other [other_offset [other_target [other_address
    [ROW [CURRENT_ROOT [CURRENT_POINTER [CURRENT_BOUND FLAG]]]]]]]]]].
  repeat rewrite PTree.gso in CURRENT_ROOT by congruence.
  assert (SAME_ROOT : Vptr other other_offset = Vptr block offset) by congruence.
  injection SAME_ROOT as BLOCK OFFSET; subst other other_offset.
  assert (SAME_POINTER : Vptr other_target other_address = Vptr target address) by congruence.
  injection SAME_POINTER as TARGET ADDRESS; subst other_target other_address.
  assert (SAME_BOUND : v = Vint bound) by congruence; subst v.
  exists block,offset,target,address,bound; cbn [entry_temps entry_memory].
  repeat rewrite PTree.gso by congruence; rewrite !PTree.gss; repeat split; assumption.
Qed.

Theorem dependent_guard_prefix_domain source (package : memory_affine_inner_pointer_package source)
  loads root pointer_cache fe ge locals temps memory captured after final :
  pointer_cache <> root -> affine_inner_pointer_bound (affine_inner_pointer_shape package) <> root ->
  affine_inner_pointer_bound (affine_inner_pointer_shape package) <> pointer_cache ->
  ~ In pointer_cache (source_load_pointers loads) ->
  ~ In (affine_inner_pointer_bound (affine_inner_pointer_shape package)) (source_load_pointers loads) ->
  source_observations_check (affine_inner_pointer_pointers package) loads = true ->
  exec_stmt fe ge locals temps memory (dependent_guard_prefix loads root pointer_cache
    (affine_inner_pointer_bound (affine_inner_pointer_shape package))) E0 captured memory Out_normal ->
  exec_stmt fe ge locals captured memory (affine_dependent_loaded_source package root) E0 after final Out_normal ->
  affine_dependent_loaded_completed package root pointer_cache fe (Entry ge locals captured memory).
Proof.
  intros POINTER_ROOT CACHE_ROOT DISTINCT POINTER_PRIVATE CACHE_PRIVATE CHECK PREFIX SOURCE.
  destruct (@source_observations_check_sound _ _ CHECK) as [COVER FRESH].
  unfold dependent_guard_prefix in PREFIX; inversion PREFIX; subst; [|contradiction].
  match goal with EMPTY : _ ** _ = E0 |- _ => apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst end.
  match goal with LOADS : exec_stmt _ _ _ _ _ (source_load_prefix loads) _ _ _ _ |- _ =>
    destruct (@source_load_prefix_observations loads _ _ _ _ _ _ _ _ _ FRESH LOADS)
      as [_ [MEMORY [_ OBSERVED]]]; subst end.
  destruct (dependent_bound_completed_header SOURCE) as [flag HEADER].
  pose proof HEADER as TYPING.
  destruct (dependent_bound_test_facts TYPING) as [counter [bound [block [offset [target [address [ROW REST]]]]]]].
  split; [exists counter; exact ROW|split; [|split; [|exists after,final; exact SOURCE]]].
  - eapply dependent_capture_header_receipt; [exact POINTER_ROOT|exact CACHE_ROOT|exact DISTINCT|eassumption|exact HEADER].
  - intros identifier MEMBER; apply COVER in MEMBER.
    destruct (OBSERVED identifier MEMBER) as [block' [offset' [BIND VALID]]].
    exists block',offset'; split; [|exact VALID].
    erewrite writes_only_frame; [exact BIND|eassumption|apply dependent_capture_writes|].
    cbn; intros [SAME|[SAME|[]]]; subst identifier; contradiction.
Qed.

Lemma source_load_pointer_is_temp loads identifier :
  In identifier (source_load_pointers loads) -> In identifier (statement_temps (source_load_prefix loads)).
Proof.
  induction loads as [|[target pointer] rest IH]; [contradiction|].
  cbn [source_load_pointers map snd source_load_prefix statement_temps expression_temps signed_load signed_pointer_temp].
  intros [SAME|MEMBER]; [subst identifier; cbn; auto|cbn; right; right; apply IH; exact MEMBER].
Qed.

Print Assumptions dependent_guard_prefix_supported.
Print Assumptions dependent_capture_header_receipt.
Print Assumptions dependent_guard_prefix_domain.
Print Assumptions source_load_pointer_is_temp.
