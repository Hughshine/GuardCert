From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestNamespace
  AffineNestDomainGuard AffineNestSourceGuard AffineNestMathDomain.
Import ListNotations.
Set Implicit Arguments.

Definition affine_package_guard_code source parameters live proposal (package:affine_guard_package source parameters live proposal) :=
  affine_domain_guard_code(affine_proposed_iterator proposal)(affine_proposed_bound proposal)
    (MemorySourceTemp(affine_proposed_bound proposal))(affine_proposed_body proposal)(affine_proposed_child proposal)
    (affine_proposed_parameter_ranges proposal) parameters(affine_proposed_floor proposal)(affine_proposed_cap proposal)
    (affine_proposal_rename proposal)(affine_proposed_result proposal).
Definition affine_package_guard_flag parameters proposal state :=
  affine_domain_guard_flag(affine_proposal_nest proposal)(affine_proposed_parameter_ranges proposal) parameters
    (affine_proposed_iterator proposal)(affine_proposed_floor proposal)(affine_proposed_cap proposal) state.

Theorem affine_package_guard_execution source parameters live proposal (package:affine_guard_package source parameters live proposal)
  fe ge locals temps memory source_after source_final :
  exec_stmt fe ge locals temps memory source E0 source_after source_final Out_normal ->
  exists after,
    exec_stmt fe ge locals temps memory(affine_package_guard_code package) E0 after memory Out_normal /\
    temp_agree(parameters++[affine_proposed_iterator proposal;affine_proposed_bound proposal]++live) temps after /\
    after!(affine_proposed_result proposal)=Some(Vint(if affine_package_guard_flag parameters proposal(Entry ge locals temps memory)
      then Int.one else Int.zero)) /\
    (affine_package_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
      affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)(affine_proposal_nest proposal)
        (affine_word_valuation temps)(affine_word_valuation temps(affine_proposed_iterator proposal))).
Proof.
  intro SOURCE.
  pose proof(affine_package_nest package) as NEST.
  pose proof(described_affine_source(affine_package_description package)) as EXACT; rewrite NEST in EXACT; rewrite EXACT in SOURCE.
  pose proof(described_affine_shapes(affine_package_description package)) as SHAPES; rewrite NEST in SHAPES.
  pose proof(@affine_nest_fresh_controls _ (described_affine_fresh(affine_package_description package))) as FRESH; rewrite NEST in FRESH.
  pose proof(described_affine_dependencies(affine_package_description package)) as DEPENDENCIES; rewrite NEST in DEPENDENCIES.
  pose proof(affine_package_namespace package) as NAMES.
  exact(@affine_source_domain_guard_execution(affine_proposed_iterator proposal)(affine_proposed_bound proposal)
    (MemorySourceTemp(affine_proposed_bound proposal))(affine_proposed_body proposal)(affine_proposed_child proposal)
    (affine_proposed_leaf_bounds proposal)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)
    (affine_proposal_layout proposal parameters) [](affine_proposed_pointers proposal)(affine_proposed_operations proposal)
    (affine_package_leaf package)(affine_proposed_parameter_ranges proposal) parameters(affine_proposed_floor proposal)(affine_proposed_cap proposal)
    (affine_proposed_remaining proposal) live(affine_probe_registry(affine_proposal_nest proposal) parameters)
    (affine_proposal_rename proposal)(affine_proposed_result proposal) fe ge locals temps memory source_after source_final
    SHAPES FRESH DEPENDENCIES(affine_package_used package)(affine_package_profile package)(affine_package_parameter_intervals package)
    (@affine_probe_registry_coverage _ _) (affine_names_injective NAMES)(affine_names_root_distinct NAMES)
    (affine_names_result_private NAMES)(affine_names_controls_private NAMES)(affine_names_parameters NAMES) SOURCE).
Qed.
Print Assumptions affine_package_guard_execution.
