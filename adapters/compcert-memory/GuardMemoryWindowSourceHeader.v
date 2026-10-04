From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightTempFrame ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryPointerSequence GuardMemoryStartedSourceWords
  GuardMemoryStartedHeader GuardMemoryVectorBounds.
From GuardMemory Require Import GuardMemoryWindowSyntax GuardMemoryWindowHeader GuardMemoryWindowFirstLeaf.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Lemma window_caps_signed caps : Forall (fun cap => 0 < cap /\ signed_range cap) caps -> Forall signed_range caps.
Proof. intro CAPS; eapply Forall_impl; [|exact CAPS]; intros cap [POSITIVE SIGNED]; exact SIGNED. Qed.
Lemma window_root_cap_last_signed caps :
  Forall (fun cap => 0 < cap /\ signed_range cap) caps -> signed_range (hd 1 caps-1).
Proof.
  intro CAPS; destruct caps as [|first rest]; cbn [hd].
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - inversion CAPS; subst; unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia.
Qed.
Lemma window_ranges_positive caps identifiers s :
  Forall2 (fun cap key => register_range key cap s) caps identifiers ->
  Forall (fun key => 0 < Int.signed (temp_word key (entry_temps s))) identifiers.
Proof. intro RANGES; induction RANGES; constructor; [exact (proj1 (proj2 H))|exact IHRANGES]. Qed.
Theorem window_source_bounds_domain source nest caps root_lower parameters parameter_bounds pointers lower upper scalars operations
  (CERT : window_source_certificate source nest caps root_lower parameters parameter_bounds pointers lower upper scalars operations)
  iterator bound body child fe ge locals temps memory after final :
  nest = MemorySourceAxis iterator bound body child ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_started_bounds_domain caps iterator bound (memory_nest_bounds nest) (Entry ge locals temps memory).
Proof.
  intros NEST SOURCE; pose proof (window_source_body CERT) as BODY.
  assert (LOOP : exec_stmt fe ge locals temps memory
    (memory_nest_source (MemorySourceAxis iterator bound body child)) E0 after final Out_normal).
  { rewrite <-NEST,<-(window_source_exact CERT); exact SOURCE. }
  assert (LENGTH : length caps = length (bound::memory_nest_bounds child)).
  { rewrite (window_source_caps_length CERT),memory_nest_lengths,NEST; reflexivity. }
  rewrite NEST in BODY; cbn [memory_nest_leaf] in BODY.
  assert (NORMAL : normal_statement (memory_nest_leaf child) = true) by (eapply memory_pointer_sequence_normal; exact BODY).
  assert (QUIET : quiet_statement (memory_nest_leaf child) = true) by (eapply memory_pointer_sequence_quiet; exact BODY).
  assert (WRITES : writes_only [] (memory_nest_leaf child)) by (eapply memory_pointer_sequence_writes; exact BODY).
  destruct (@memory_started_source_vector_bounds fe ge locals iterator bound body child caps temps memory after final
    LENGTH (window_caps_signed (window_source_caps CERT))
    ltac:(rewrite <-NEST; exact (window_source_shapes CERT)) ltac:(rewrite <-NEST; exact (window_source_fresh CERT))
    NORMAL QUIET WRITES LOOP) as [ITERATOR [BOUND DOMAIN]].
  unfold memory_started_bounds_domain; split; [exact ITERATOR|split; [exact BOUND|]].
  intro ACTIVE; rewrite NEST; apply DOMAIN; apply memory_started_active_true in ACTIVE; exact ACTIVE.
Qed.
Theorem window_source_header_domain source nest caps root_lower parameters parameter_bounds pointers lower upper scalars operations
  (CERT : window_source_certificate source nest caps root_lower parameters parameter_bounds pointers lower upper scalars operations)
  iterator bound body child fe ge locals temps memory after final :
  nest = MemorySourceAxis iterator bound body child ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  window_header_domain root_lower (hd 1 caps) caps iterator bound (memory_nest_bounds nest) parameters (Entry ge locals temps memory).
Proof.
  intros NEST SOURCE.
  pose proof (@window_source_bounds_domain _ _ _ _ _ _ _ _ _ _ _ CERT iterator bound body child
    fe ge locals temps memory after final NEST SOURCE) as DOMAIN.
  split; [exact DOMAIN|]; intro ACCEPT.
  destruct (@window_bounds_sound root_lower (hd 1 caps) caps iterator bound (memory_nest_bounds nest)
    (Entry ge locals temps memory) (proj1 (window_source_root_lower CERT))
    (window_root_cap_last_signed (window_source_caps CERT)) (window_caps_signed (window_source_caps CERT)) DOMAIN ACCEPT)
    as [ACTIVE [ROOT RANGES]].
  assert (POSITIVE : Forall (fun key => 0 < Int.signed (temp_word key temps)) (memory_nest_bounds nest)).
  { exact (window_ranges_positive RANGES). }
  rewrite NEST in POSITIVE; inversion POSITIVE as [|same keys POS CHILD_POS]; subst same keys.
  apply Forall_forall; intros identifier MEMBER.
  destruct (@window_source_first_capability _ _ _ _ _ _ _ _ _ _ _ CERT iterator bound body child
    fe ge locals temps memory after final NEST ltac:(assumption) (proj2 ACTIVE) SOURCE identifier
    ltac:(apply in_or_app; left; exact MEMBER)) as [word WORD].
  exists word; exact WORD.
Qed.
Print Assumptions window_source_header_domain.
