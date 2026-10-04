From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestMathDomain AffineNestProfile
  AffineNestProfileSound AffineNestNumericGuard AffineNestDomainGuard AffineNestSourceDecode.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma affine_controls_iterators_unique nest : NoDup(affine_nest_controls nest) -> NoDup(affine_nest_iterators nest).
Proof.
  induction nest; intro UNIQUE; [constructor|].
  inversion UNIQUE as [|first rest ITERATOR_FRESH TAIL]; subst.
  inversion TAIL as [|first rest BOUND_FRESH CHILD_FRESH]; subst; constructor.
  - intro MEMBER; apply ITERATOR_FRESH; cbn; right.
    apply affine_nest_controls_member; auto.
  - apply IHnest; exact CHILD_FRESH.
Qed.
Lemma affine_iterators_mutated nest identifier : In identifier(affine_nest_iterators nest) -> In identifier(affine_nest_mutated nest).
Proof.
  destruct nest; [contradiction|].
  cbn [affine_nest_iterators affine_nest_mutated List.In]; intros [HEAD|CHILD]; [auto|right].
  apply affine_nest_controls_member; auto.
Qed.

Theorem affine_domain_guard_accepted iterator bound expression body child parameter_ranges parameters floor cap remaining
  leaf_bounds leaf_layout state :
  check_affine_math_profile (AffineSourceAxis iterator bound expression body child) [] parameters [] parameter_ranges
    ((floor,cap)::remaining) leaf_bounds leaf_layout=true ->
  affine_parameter_intervals_check parameter_ranges=true ->
  NoDup(affine_nest_controls(AffineSourceAxis iterator bound expression body child)) ->
  (forall identifier, In identifier parameters -> ~In identifier(affine_nest_mutated(AffineSourceAxis iterator bound expression body child))) ->
  affine_domain_guard_flag(AffineSourceAxis iterator bound expression body child) parameter_ranges parameters iterator floor cap state=true ->
  affine_math_domain leaf_bounds leaf_layout(AffineSourceAxis iterator bound expression body child)
    (affine_word_valuation(entry_temps state))(affine_word_valuation(entry_temps state) iterator).
Proof.
  intros CHECK PARAMETER_CHECK UNIQUE FRESH ACCEPT.
  pose proof CHECK as ROOT_CHECK; cbn [check_affine_math_profile] in ROOT_CHECK.
  rewrite !andb_true_iff in ROOT_CHECK; destruct ROOT_CHECK as [[[[[FLOOR CAP] NONEMPTY] BOUND] CHILD_START] CHILD_CHECK].
  apply affine_signed_range_check_sound in FLOOR,CAP; apply Z.ltb_lt in NONEMPTY.
  assert (CAP_LAST:signed_range(cap-1)) by (unfold signed_range in *; lia).
  apply andb_true_iff in ACCEPT as [ACTIVE NUMERIC].
  destruct(@affine_numeric_guard_sound parameter_ranges parameters iterator floor cap state PARAMETER_CHECK FLOOR CAP_LAST NUMERIC)
    as [PARAMETERS START].
  eapply checked_affine_profile_domain with(prefix:=[]) (parameters:=parameters) (prefix_ranges:=[])
    (parameter_ranges:=parameter_ranges) (axis_ranges:=(floor,cap)::remaining); [exact CHECK| | | |exact PARAMETERS| |].
  - apply affine_controls_iterators_unique; exact UNIQUE.
  - intros identifier MEMBER BAD; cbn in BAD.
    apply(FRESH identifier BAD),affine_iterators_mutated; exact MEMBER.
  - constructor.
  - unfold affine_word_valuation,signed_range; apply Int.signed_range.
  - exact(proj1 START).
Qed.
Print Assumptions affine_controls_iterators_unique.
Print Assumptions affine_domain_guard_accepted.
