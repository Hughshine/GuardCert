From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageGuard
  AffineNestDomainGuard AffineNestProbe AffineNestGuardDomain AffineNestValuation AffineNestFirstDomain AffineNestLeafModel.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_package_accepted_word_view source parameters live proposal
  (package:affine_guard_package source parameters live proposal) fe ge locals temps memory after final :
  affine_package_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  affine_word_view parameters(affine_word_valuation temps) temps.
Proof.
  intros ACCEPT SOURCE.
  unfold affine_package_guard_flag,affine_domain_guard_flag in ACCEPT.
  apply andb_true_iff in ACCEPT as [ACTIVE NUMERIC].
  cbn [entry_temps] in ACTIVE; apply affine_first_path_flag_exact in ACTIVE.
  pose proof(affine_package_nest package) as NEST.
  pose proof(described_affine_source(affine_package_description package)) as EXACT; rewrite NEST in EXACT; rewrite EXACT in SOURCE.
  pose proof(described_affine_shapes(affine_package_description package)) as SHAPES; rewrite NEST in SHAPES.
  pose proof(@affine_nest_fresh_controls _ (described_affine_fresh(affine_package_description package))) as FRESH; rewrite NEST in FRESH.
  apply affine_register_domains_word_view with(ge:=ge)(locals:=locals)(memory:=memory).
  exact(@affine_source_guard_parameter_domains(affine_proposal_nest proposal)
    (affine_proposed_leaf_bounds proposal)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)
    (affine_proposal_layout proposal parameters) [](affine_proposed_pointers proposal)(affine_proposed_operations proposal)
    (affine_package_leaf package) parameters fe ge locals temps memory after final
    (affine_package_used package) SHAPES FRESH ACTIVE SOURCE).
Qed.

Theorem affine_package_root_words source parameters live proposal
  (package:affine_guard_package source parameters live proposal) fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  (exists word,temps!(affine_proposed_iterator proposal)=Some(Vint word)) /\
  (exists word,temps!(affine_proposed_bound proposal)=Some(Vint word)).
Proof.
  intro SOURCE.
  pose proof(affine_package_nest package) as NEST.
  pose proof(described_affine_source(affine_package_description package)) as EXACT; rewrite NEST in EXACT; rewrite EXACT in SOURCE.
  pose proof(described_affine_shapes(affine_package_description package)) as SHAPES; rewrite NEST in SHAPES.
  pose proof(@affine_nest_fresh_controls _ (described_affine_fresh(affine_package_description package))) as FRESH; rewrite NEST in FRESH.
  pose proof(@affine_source_first_header_domain(affine_proposal_nest proposal) fe ge locals temps memory after final
    SHAPES FRESH (affine_leaf_normal(affine_package_leaf package))(affine_leaf_quiet(affine_package_leaf package))
    (affine_leaf_writes(affine_package_leaf package)) SOURCE) as DOMAIN.
  exact(conj(proj1 DOMAIN)(proj1(proj2 DOMAIN))).
Qed.
Print Assumptions affine_package_accepted_word_view.
Print Assumptions affine_package_root_words.
