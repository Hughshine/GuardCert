From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightRedundantSet.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceShape
  AffineNestFirstDomain AffineNestCapturedDomain AffineNestLeafModel AffineNestGuardPackage
  AffineNestNamespace AffineNestPackageGuard AffineNestProbeStage AffineNestDomainGuard
  AffineNestGuardParameterCheck AffineNestAcceptedDomain AffineNestMathDomain.
From GuardInterface Require Import ClightAffineNestMaterialized.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_captured_package_guard_execution source parameters live proposal
  (package : affine_guard_package source parameters live proposal) fe ge locals temps memory :
  register_domain (affine_proposed_iterator proposal) (Entry ge locals temps memory) ->
  register_domain (affine_proposed_bound proposal) (Entry ge locals temps memory) ->
  Forall (fun id=>register_domain id (Entry ge locals temps memory)) parameters ->
  exists after,
    exec_stmt fe ge locals temps memory (affine_package_guard_code package) E0 after memory Out_normal /\
    temp_agree (affine_single_materialized_ports parameters proposal live) temps after /\
    after!(affine_proposed_result proposal)=Some(Vint(if affine_package_guard_flag parameters proposal
      (Entry ge locals temps memory) then Int.one else Int.zero)) /\
    (affine_package_guard_flag parameters proposal (Entry ge locals temps memory)=true ->
     affine_math_domain (affine_proposed_leaf_bounds proposal) (affine_proposal_layout proposal parameters)
       (affine_proposal_nest proposal) (affine_word_valuation temps)
       (affine_word_valuation temps (affine_proposed_iterator proposal))).
Proof.
  intros ROW BOUND PARAMETERS; pose proof (affine_package_nest package) as NEST.
  pose proof (described_affine_dependencies (affine_package_description package)) as DEPENDENCIES;
    rewrite NEST in DEPENDENCIES.
  assert (DOMAIN : affine_first_header_domain (affine_proposal_nest proposal) temps).
  { eapply affine_captured_parameters_first_headers; [exact DEPENDENCIES| |exact ROW|exact BOUND].
    intros id MEMBER; apply Forall_forall with (x:=id) in PARAMETERS; [exact PARAMETERS|exact MEMBER]. }
  pose proof (affine_package_namespace package) as NAMES.
  destruct (@affine_domain_guard_execution (affine_proposed_iterator proposal) (affine_proposed_bound proposal)
    (MemorySourceTemp (affine_proposed_bound proposal)) (affine_proposed_body proposal) (affine_proposed_child proposal)
    (affine_proposed_parameter_ranges proposal) parameters (affine_proposed_floor proposal) (affine_proposed_cap proposal)
    live (affine_probe_registry (affine_proposal_nest proposal) parameters) (affine_proposal_rename proposal)
    (affine_proposed_result proposal) fe ge locals temps memory DEPENDENCIES
    (@affine_probe_registry_coverage _ _) (affine_names_injective NAMES) (affine_names_root_distinct NAMES)
    (affine_names_result_private NAMES) (affine_names_controls_private NAMES) (affine_names_parameters NAMES)
    DOMAIN ltac:(intro ACTIVE; exact PARAMETERS)) as [after [RUN [FRAME RESULT]]].
  exists after; split; [exact RUN|split; [exact FRAME|split; [exact RESULT|]]].
  intro ACCEPT; eapply (@affine_domain_guard_accepted (affine_proposed_iterator proposal) (affine_proposed_bound proposal)
    (MemorySourceTemp (affine_proposed_bound proposal)) (affine_proposed_body proposal) (affine_proposed_child proposal)
    (affine_proposed_parameter_ranges proposal) parameters (affine_proposed_floor proposal) (affine_proposed_cap proposal)
    (affine_proposed_remaining proposal) (affine_proposed_leaf_bounds proposal) (affine_proposal_layout proposal parameters)
    (Entry ge locals temps memory));
    [exact (affine_package_profile package)|exact (affine_package_parameter_intervals package)| | |exact ACCEPT].
  - pose proof (@affine_nest_fresh_controls _ (described_affine_fresh (affine_package_description package))) as FRESH;
      rewrite NEST in FRESH; exact FRESH.
  - intros id MEMBER; exact (proj2 (@check_affine_guard_parameters_sound _ _ _ _ _ (affine_package_used package) id MEMBER)).
Qed.

Print Assumptions affine_captured_package_guard_execution.
