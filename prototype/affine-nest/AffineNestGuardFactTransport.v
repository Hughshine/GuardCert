From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstLeaf
  AffineNestProbe AffineNestProbeStage AffineNestProbeRenaming AffineNestDomainGuard
  AffineNestNumericExecution AffineNestGuardPackage AffineNestPackageGuard.
Import ListNotations.
Set Implicit Arguments.

(** Future public child controls need not be initialized or preserved. Each
    private first-path probe initializes them from earlier coordinates. *)
Theorem affine_first_path_flag_frame nest : forall prefix parameters before after,
  affine_nest_bound_dependencies prefix parameters nest ->
  temp_agree (affine_probe_needed nest prefix parameters) before after ->
  affine_first_path_flag nest after=affine_first_path_flag nest before.
Proof.
  induction nest as [leaf|iterator bound expression body child IH];
    intros prefix parameters before after DEPENDENCIES FRAME; [reflexivity|].
  assert(ROW:after!iterator=before!iterator).
  { apply FRAME; unfold affine_probe_needed; apply in_or_app; right; cbn; auto. }
  assert(BOUND:after!bound=before!bound).
  { apply FRAME; unfold affine_probe_needed; apply in_or_app; right; cbn; auto. }
  cbn [affine_first_path_flag]; unfold temp_word at 1 2; rewrite ROW,BOUND.
  fold (temp_word iterator before) (temp_word bound before).
  destruct(Int.lt(temp_word iterator before)(temp_word bound before)); [|reflexivity].
  destruct child as [code|child_iterator child_bound child_expression child_body grandchild]; [reflexivity|].
  assert(MATH:memory_source_affine_math(affine_word_valuation after) child_expression=
    memory_source_affine_math(affine_word_valuation before) child_expression).
  { apply affine_expression_math_frame; intros identifier MEMBER.
    unfold affine_word_valuation,temp_word; rewrite FRAME; [reflexivity|].
    eapply affine_probe_stage_child_reads; eassumption. }
  apply (IH (prefix++[iterator]) parameters); [exact(proj2 DEPENDENCIES)|].
  cbn [affine_first_child_temps]; rewrite MATH.
  intros identifier MEMBER.
  rewrite !PTree.gsspec.
  destruct(peq identifier child_iterator) as [SAME|NOT_ITERATOR]; [reflexivity|].
  destruct(peq identifier child_bound) as [SAME|NOT_BOUND]; [reflexivity|].
  apply FRAME; unfold affine_probe_needed in *; repeat rewrite in_app_iff in *;
    cbn [List.In] in *; intuition congruence.
Qed.

Theorem affine_package_guard_flag_frame source parameters live proposal
  (package:affine_guard_package source parameters live proposal) ge locals memory before after :
  temp_agree(parameters++[affine_proposed_iterator proposal;affine_proposed_bound proposal]) before after ->
  affine_package_guard_flag parameters proposal(Entry ge locals after memory)=
    affine_package_guard_flag parameters proposal(Entry ge locals before memory).
Proof.
  intro FRAME; unfold affine_package_guard_flag,affine_domain_guard_flag; cbn [entry_temps].
  rewrite (@affine_first_path_flag_frame (affine_proposal_nest proposal) [] parameters before after).
  - rewrite (@affine_numeric_guard_flag_frame (affine_proposed_parameter_ranges proposal) parameters
      (affine_proposed_iterator proposal)(affine_proposed_floor proposal)(affine_proposed_cap proposal)
      ge locals before after memory); [reflexivity|].
    intros identifier MEMBER; apply FRAME; repeat rewrite in_app_iff in *; cbn [List.In] in *; tauto.
  - pose proof(described_affine_dependencies(affine_package_description package)) as DEPENDENCIES.
    rewrite(affine_package_nest package) in DEPENDENCIES; exact DEPENDENCIES.
  - exact FRAME.
Qed.

Print Assumptions affine_first_path_flag_frame.
Print Assumptions affine_package_guard_flag_frame.
