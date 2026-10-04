From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryPointerBackend GuardMemoryFramedNested
  GuardMemoryIntervalBox GuardMemoryParametricGuard GuardMemoryParametricSourceDomain.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard
  AffineNestPackageWords AffineNestPackageDecode AffineNestProfile AffineNestNumericGuard AffineNestDomainGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_package_ranges proposal := affine_proposed_parameter_ranges proposal++
  [(affine_proposed_floor proposal,affine_proposed_cap proposal)].
Definition affine_package_validator_bounds proposal := map affine_profile_interval(affine_package_ranges proposal).
Definition affine_package_encoder_bounds proposal := map(fun range=>MemoryFramedNested.N.A.Interval(fst range)(snd range-1))
  (affine_package_ranges proposal).

Theorem affine_package_accepted_ranges source parameters live proposal
  (package:affine_guard_package source parameters live proposal) state :
  affine_package_guard_flag parameters proposal state=true ->
  interval_ranges(affine_package_ranges proposal)
    (map(affine_word_valuation(entry_temps state))(affine_package_context parameters proposal)).
Proof.
  intro ACCEPT; unfold affine_package_guard_flag,affine_domain_guard_flag in ACCEPT; apply andb_true_iff in ACCEPT as [ACTIVE NUMERIC].
  pose proof(affine_package_profile package) as CHECK.
  cbn [check_affine_math_profile affine_proposal_nest] in CHECK.
  rewrite !andb_true_iff in CHECK; destruct CHECK as [[[[[FLOOR CAP] NONEMPTY] BOUND] START] CHILD].
  apply affine_signed_range_check_sound in FLOOR,CAP; apply Z.ltb_lt in NONEMPTY.
  assert (CAP_LAST:signed_range(affine_proposed_cap proposal-1)) by(unfold signed_range in *; lia).
  destruct(@affine_numeric_guard_sound _ _ _ _ _ _ (affine_package_parameter_intervals package) FLOOR CAP_LAST NUMERIC)
    as [PARAMETERS ROOT].
  unfold affine_package_ranges,affine_package_context; rewrite map_app; cbn [map].
  unfold interval_ranges in *; apply Forall2_app; [exact PARAMETERS|constructor; [exact ROOT|constructor]].
Qed.

Theorem affine_package_validator_within source parameters live proposal
  (package:affine_guard_package source parameters live proposal) state :
  affine_package_guard_flag parameters proposal state=true ->
  MemoryNested.A.env_within(affine_package_validator_bounds proposal)
    (map(affine_word_valuation(entry_temps state))(affine_package_context parameters proposal)).
Proof. intro ACCEPT; apply affine_profile_ranges_within; exact(@affine_package_accepted_ranges _ _ _ _ package state ACCEPT). Qed.

Lemma affine_encoder_ranges_within ranges values : interval_ranges ranges values ->
  MemoryFramedNested.N.A.env_within(map(fun range=>MemoryFramedNested.N.A.Interval(fst range)(snd range-1)) ranges) values.
Proof.
  intro RANGES; induction RANGES; cbn [map].
  - intros index bound LOOKUP; destruct index; discriminate.
  - apply MemoryFramedNested.N.A.env_within_cons; [|exact IHRANGES].
    unfold MemoryFramedNested.N.A.contains; cbn; lia.
Qed.

Theorem affine_package_encoder_within source parameters live proposal
  (package:affine_guard_package source parameters live proposal) state :
  affine_package_guard_flag parameters proposal state=true ->
  MemoryFramedNested.N.A.env_within(affine_package_encoder_bounds proposal)
    (map(affine_word_valuation(entry_temps state))(affine_package_context parameters proposal)).
Proof. intro ACCEPT; apply affine_encoder_ranges_within; exact(@affine_package_accepted_ranges _ _ _ _ package state ACCEPT). Qed.

Theorem affine_package_context_typed source parameters live proposal
  (package:affine_guard_package source parameters live proposal) fe ge locals temps memory after final :
  affine_package_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  MemoryNested.A.typed_view(affine_package_context parameters proposal)
    (map(affine_word_valuation temps)(affine_package_context parameters proposal)) temps.
Proof.
  intros ACCEPT SOURCE.
  pose proof(@affine_package_accepted_word_view _ _ _ _ package fe ge locals temps memory after final ACCEPT SOURCE) as WORDS.
  destruct(@affine_package_root_words _ _ _ _ package fe ge locals temps memory after final SOURCE) as [ROOT BOUND].
  change(MemoryNested.A.typed_view(affine_package_context parameters proposal)
    (memory_source_parameter_values(affine_package_context parameters proposal)(Entry ge locals temps memory)) temps).
  apply memory_source_parameter_view; intros identifier MEMBER.
  unfold affine_package_context in MEMBER; apply in_app_or in MEMBER as [PARAMETER|ITERATOR].
  - exists(Int.repr(affine_word_valuation temps identifier)); apply WORDS; exact PARAMETER.
  - cbn in ITERATOR; destruct ITERATOR as [SAME|BAD]; [subst; exact ROOT|contradiction].
Qed.
Print Assumptions affine_package_validator_within.
Print Assumptions affine_package_encoder_within.
Print Assumptions affine_package_context_typed.
